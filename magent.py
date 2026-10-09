#  This file is part of KGPixModules
#  Copyright (c) 2025-2026 @kgpix
#  This software is released under the MIT License.
#  https://opensource.org/licenses/MIT

# scope heroku_min: 2.0.0

__version__ = ("1", "4", "4")

# meta developer: @kgpix

import re
import os
import io
import random
import socket
import base64
import uuid
import json
import asyncio
import contextlib
import logging
import tempfile
import time
import aiohttp
from markdown_it import MarkdownIt
import pytz
import httpx

# New SDK Check
try:
    from google import genai
    from google.genai import types
    import google.api_core.exceptions as google_exceptions
    GOOGLE_AVAILABLE = True
except ImportError:
    GOOGLE_AVAILABLE = False
    google_exceptions = None

from PIL import Image
from datetime import datetime
from telethon import types as tg_types
from telethon.tl.types import Message, DocumentAttributeFilename, DocumentAttributeSticker
from telethon.utils import get_display_name, get_peer_id
from telethon.errors.rpcerrorlist import (
    MessageTooLongError, 
    ChatAdminRequiredError,
    UserNotParticipantError, 
    ChannelPrivateError
)

from .. import loader, utils
from ..inline.types import InlineCall

logger = logging.getLogger(__name__)

_gemini_log_client = None
_gemini_log_channel = None
_gemini_log_topic_id = None

class _GeminiTopicHandler(logging.Handler):
    def emit(self, record):
        if _gemini_log_client is None or _gemini_log_channel is None or _gemini_log_topic_id is None:
            return
        try:
            text = f"<code>[{record.levelname}]</code> {self.format(record)}"
            asyncio.ensure_future(
                _gemini_log_client.send_message(
                    int(f"-100{_gemini_log_channel}"),
                    text,
                    parse_mode="html",
                    reply_to=_gemini_log_topic_id,
                )
            )
        except Exception:
            pass

_gemini_topic_handler = _GeminiTopicHandler()
_gemini_topic_handler.setLevel(logging.WARNING)
logger.addHandler(_gemini_topic_handler)

DB_HISTORY_KEY = "gemini_conversations_v4"
DB_GAUTO_HISTORY_KEY = "gemini_gauto_conversations_v1"
DB_IMPERSONATION_KEY = "gemini_impersonation_chats"
DB_PRESETS_KEY = "gemini_prompt_presets"
DB_PAGER_CACHE_KEY = "gemini_pager_cache"
DB_KEY_MAP_KEY = "gemini_key_model_map"
DB_MEMORY_DISABLED_KEY = "gemini_memory_disabled_chats"
DB_SESSION_STATS_KEY = "gemini_session_stats_v1"
DB_PROVIDER_MODELS_KEY = "gemini_provider_models_v1"
DB_SKILLS_KEY = "gemini_skills_v1"
DB_PROVIDER_STATE_KEY = "gemini_provider_state_v1"
GEMINI_TIMEOUT = 840
MAX_FFMPEG_SIZE = 90 * 1024 * 1024
CHECK_MODEL = "gemini-2.5-pro"  
MODEL_PROFILE_CHOICES = ("auto", "balanced", "fast", "reasoning", "coding", "vision", "manual")

# requires: google-genai google-api-core pytz markdown_it_py aiohttp-socks

# =========================================================================
# KeyTest module-level data & checkers (by @kgpix) — used by .keytest/.kprov
# =========================================================================
# ---------------------------------------------------------------------------
# Balance parsers for GET account/balance endpoints -> (verdict, balance_str)
# ---------------------------------------------------------------------------

_ELEVEN_TIER = {
    "free": "Free", "starter": "Starter", "creator": "Creator", "independent": "Independent",
    "growing": "Growing", "growing_business": "Growing", "pro": "Pro",
    "scale": "Scale", "scale_2024_08_10": "Scale", "business": "Business",
    "enterprise": "Enterprise", "trial": "Trial",
}
def _bal_elevenlabs(j):
    used = j.get("character_count") or 0
    lim = j.get("character_limit") or 0
    tier = j.get("tier") or ""
    status = j.get("status") or ""
    if not lim:
        return ("valid", None, _ELEVEN_TIER.get(tier, tier) or None)
    rem = lim - used
    info_parts = [_ELEVEN_TIER.get(tier, tier)] if tier else []
    if status and status not in ("active", "free", "trialing"):
        info_parts.append(status)
    return (("no_balance" if rem <= 0 else "valid"), "%s chars" % rem, " · ".join(info_parts) or None)


def _bal_leonardo(j):
    ud = (j.get("user_details") or [{}])
    d = ud[0] if ud else {}
    tok = d.get("apiSubscriptionTokens", d.get("subscriptionTokens"))
    if tok is None:
        return ("valid", None)
    return (("no_balance" if tok == 0 else "valid"), "%s tokens" % tok)


def _bal_recraft(j):
    c = j.get("credits")
    return ("valid", None) if c is None else (("no_balance" if c == 0 else "valid"), "%s credits" % c)


def _bal_runway(j):
    c = j.get("creditBalance")
    return ("valid", None) if c is None else (("no_balance" if c == 0 else "valid"), "%s credits" % c)


def _bal_heygen(j):
    q = (j.get("data") or {}).get("remaining_quota")
    return ("valid", None) if q is None else (("no_balance" if q == 0 else "valid"), "%s" % q)


def _bal_removebg(j):
    try:
        attrs = j["data"]["attributes"]
        c = attrs["credits"]["total"]
        sub = attrs["credits"].get("subscription", 0)
        payg = attrs["credits"].get("payg", 0)
        sizes = attrs.get("api", {}).get("sizes", "")
        info_parts = []
        if sub:
            info_parts.append("sub %s" % sub)
        if payg:
            info_parts.append("payg %s" % payg)
        if sizes:
            info_parts.append(sizes)
        return (("no_balance" if c == 0 else "valid"), "%s credits" % c, " · ".join(info_parts) or None)
    except Exception:  # noqa: BLE001
        return ("valid", None, None)


def _bal_revai(j):
    b = j.get("total_balance")  # balance_seconds is deprecated (always 0)
    email = j.get("email") or ""
    info = email or None
    return ("valid", None, info) if b is None else (("no_balance" if b == 0 else "valid"), "%s" % b, info)


def _bal_moonshot(j):
    d = j.get("data") or {}
    b = d.get("available_balance")
    if b is None:
        return ("valid", None, None)
    v = "no_balance" if b <= 0 else "valid"
    bal = "$%s" % b
    voucher = d.get("voucher_balance") or 0
    cash = d.get("cash_balance") or 0
    info = None
    if voucher or cash:
        info = "voucher $%s · cash $%s" % (voucher, cash)
    return (v, bal, info)


def _bal_stepfun(j):
    b = j.get("balance")
    if b is None:
        return ("valid", None, None)
    plan_type = j.get("type") or ""
    info = plan_type.capitalize() if plan_type else None
    vchr = j.get("total_voucher_balance") or 0
    if vchr:
        info = (info + " · " if info else "") + "voucher %s" % vchr
    return (("no_balance" if b == 0 else "valid"), "%s" % b, info)


def _bal_siliconflow(j):
    d = j.get("data") or {}
    b = d.get("totalBalance")
    if b is None:
        return ("valid", None, None)
    v = "no_balance" if str(b) in ("0", "0.0") else "valid"
    name = d.get("name") or ""
    email = d.get("email") or ""
    status = d.get("status") or ""
    info_parts = [x for x in [name, email] if x]
    if status and status != "normal":
        info_parts.append(status)
    return (v, "%s" % b, " · ".join(info_parts) or None)


def _bal_novita(j):
    b = j.get("availableBalance")
    if b is None:
        return ("valid", None, None)
    v = "no_balance" if b <= 0 else "valid"
    pending = j.get("pendingCharges") or 0
    info = "pending $%.2f" % (pending / 10000) if pending else None
    return (v, "$%.2f" % (b / 10000), info)


def _bal_vercel(j):
    b = j.get("balance")
    if b is None:
        return ("valid", None, None)
    used = j.get("total_used")
    info = "used $%s" % used if used else None
    return (("no_balance" if str(b) in ("0", "0.0") else "valid"), "$%s" % b, info)


def _bal_bfl(j):
    c = j.get("credits")
    return ("valid", None) if c is None else (("no_balance" if c == 0 else "valid"), "%s credits" % c)


def _bal_segmind(j):
    c = j.get("credits")
    return ("valid", None) if c is None else (("no_balance" if c == 0 else "valid"), "%s credits" % c)


def _bal_photoroom(j):
    imgs = j.get("images") or {}
    a = imgs.get("available")
    if a is None:
        return ("valid", None, None)
    plan = j.get("plan") or ""
    sub = imgs.get("subscription")
    info_parts = [plan] if plan else []
    if sub is not None:
        info_parts.append("sub %s" % sub)
    return (("no_balance" if a == 0 else "valid"), "%s images" % a, " · ".join(info_parts) or None)


def _bal_luma(j):
    c = j.get("credit_balance")
    return ("valid", None, None) if c is None else (("no_balance" if c <= 0 else "valid"), "$%.2f" % (c / 100), None)


def _bal_vidu(j):
    rem = j.get("remains") or []
    total = sum((r.get("credit_remain") or 0) for r in rem)
    return ("no_balance" if total == 0 else "valid"), "%s credits" % total


def _info_replicate(j):
    uname = j.get("username", "?")
    utype = j.get("type", "user")
    return ("valid", uname, utype if utype != "user" else None)


def _info_hf(j):
    name = j.get("name", "?")
    is_pro = j.get("isPro", False)
    info = "Pro" if is_pro else None
    return ("valid", "@%s" % name, info)


def _bal_hyperbolic(j):
    c = j.get("credits")
    if c is None:
        return ("valid", None)
    usd = c / 100
    return ("no_balance" if usd <= 0 else "valid"), ("$%.2f" % usd if usd else None)


def _bal_deepinfra(j):
    # stripe_balance: negative = credit available, positive = debt owed
    c = (j.get("checklist") or {}).get("stripe_balance")
    name = j.get("name") or j.get("display_name") or ""
    email = j.get("email") or ""
    billing = (j.get("checklist") or {}).get("billing_type") or ""
    is_biz = j.get("is_business_account") or False
    info_parts = [x for x in [name, email] if x]
    if billing:
        info_parts.append(billing)
    elif is_biz:
        info_parts.append("business")
    info = " · ".join(info_parts) or None
    if c is None:
        return ("valid", None, info)
    if c < 0:
        return ("valid", "$%.2f" % abs(c), info)
    if c == 0:
        return ("no_balance", None, info)
    return ("no_balance", "debt $%.2f" % c, info)


def _bal_chutes(j):
    b = j.get("balance")
    if b is None:
        return ("valid", None, None)
    username = j.get("username") or ""
    return ("no_balance" if b <= 0 else "valid"), ("$%.2f" % b if b else None), (username or None)


# ---------------------------------------------------------------------------
# Provider registry.  cat: chat|infra|image|video|voice|music|embed
# Entries with "method" are checkable; entries without it are listing-only.
# method: chat|embed|probe|get|special ; auth: bearer|anthropic|xi|token|raw|
#         xkey|xapikey|apikey|cartesia|runway
# ---------------------------------------------------------------------------

SPECS = {
    # ===== model labs / chat =====
    "openai": {"n": "OpenAI", "cat": "chat", "method": "chat", "url": "https://api.openai.com/v1/chat/completions", "model": "gpt-5.5", "auth": "bearer", "prefix": ["sk-proj-", "sk-svcacct-"]},
    "anthropic": {"n": "Anthropic", "cat": "chat", "method": "chat", "url": "https://api.anthropic.com/v1/messages", "model": "claude-opus-4-8", "auth": "anthropic", "prefix": ["sk-ant-"]},
    "google": {"n": "Google Gemini", "cat": "chat", "method": "special", "prefix": ["AIza"]},
    "xai": {"n": "xAI Grok", "cat": "chat", "method": "chat", "url": "https://api.x.ai/v1/chat/completions", "model": "grok-4.3", "auth": "bearer", "prefix": ["xai-"]},
    "deepseek": {"n": "DeepSeek", "cat": "chat", "method": "special"},
    "mistral": {"n": "Mistral", "cat": "chat", "method": "chat", "url": "https://api.mistral.ai/v1/chat/completions", "model": "mistral-medium-latest", "auth": "bearer"},
    "cohere": {"n": "Cohere", "cat": "chat", "method": "special"},
    "perplexity": {"n": "Perplexity", "cat": "chat", "method": "chat", "url": "https://api.perplexity.ai/chat/completions", "model": "sonar-reasoning-pro", "auth": "bearer", "prefix": ["pplx-"]},
    "ai21": {"n": "AI21", "cat": "chat", "method": "chat", "url": "https://api.ai21.com/studio/v1/chat/completions", "model": "jamba-large", "auth": "bearer"},
    "moonshot": {"n": "Moonshot Kimi", "cat": "chat", "method": "get", "url": "https://api.moonshot.ai/v1/users/me/balance", "model": "kimi-k2.6", "auth": "bearer", "balance": _bal_moonshot},
    "qwen": {"n": "Qwen / DashScope", "cat": "chat", "method": "chat", "url": "https://dashscope-intl.aliyuncs.com/compatible-mode/v1/chat/completions", "model": "qwen3-max", "auth": "bearer"},
    "zhipu": {"n": "Zhipu GLM", "cat": "chat", "method": "chat", "url": "https://api.z.ai/api/paas/v4/chat/completions", "model": "glm-5.1", "auth": "bearer"},
    "minimax": {"n": "MiniMax", "cat": "chat", "method": "special"},
    "baichuan": {"n": "Baichuan", "cat": "chat", "method": "chat", "url": "https://api.baichuan-ai.com/v1/chat/completions", "model": "Baichuan4", "auth": "bearer"},
    "stepfun": {"n": "StepFun", "cat": "chat", "method": "get", "url": "https://api.stepfun.com/v1/accounts", "model": "step-3", "auth": "bearer", "balance": _bal_stepfun},
    "reka": {"n": "Reka", "cat": "chat", "method": "chat", "url": "https://api.reka.ai/v1/chat/completions", "model": "reka-flash", "auth": "xapikey"},
    "writer": {"n": "Writer Palmyra", "cat": "chat", "method": "chat", "url": "https://api.writer.com/v1/chat/completions", "model": "palmyra-x5", "auth": "bearer"},
    "yi": {"n": "01.AI Yi", "cat": "chat", "method": "chat", "url": "https://api.lingyiwanwu.com/v1/chat/completions", "model": "yi-large", "auth": "bearer"},
    "hunyuan": {"n": "Tencent Hunyuan", "cat": "chat", "method": "chat", "url": "https://api.hunyuan.cloud.tencent.com/v1/chat/completions", "model": "hunyuan-turbos-latest", "auth": "bearer"},
    "qianfan": {"n": "Baidu ERNIE", "cat": "chat", "method": "chat", "url": "https://qianfan.baidubce.com/v2/chat/completions", "model": "ernie-5.0", "auth": "bearer"},
    "spark": {"n": "iFlytek Spark", "cat": "chat", "method": "chat", "url": "https://spark-api-open.xf-yun.com/v1/chat/completions", "model": "4.0Ultra", "auth": "bearer"},
    "upstage": {"n": "Upstage Solar", "cat": "chat", "method": "chat", "url": "https://api.upstage.ai/v1/chat/completions", "model": "solar-pro2", "auth": "bearer", "prefix": ["up_"]},
    "twoai": {"n": "Two AI SUTRA", "cat": "chat", "method": "chat", "url": "https://api.two.ai/v2/chat/completions", "model": "sutra-v2", "auth": "bearer"},
    "nscale": {"n": "Nscale", "cat": "infra", "method": "chat", "url": "https://inference.api.nscale.com/v1/chat/completions", "model": "Qwen/Qwen3-235B-A22B-Instruct", "auth": "bearer"},
    "nous": {"n": "Nous Research", "cat": "infra", "method": "chat", "url": "https://inference-api.nousresearch.com/v1/chat/completions", "model": "Hermes-4-405B", "auth": "bearer"},
    "krutrim": {"n": "Krutrim", "cat": "infra", "method": "chat", "url": "https://cloud.krutrim.com/api/v1/chat/completions", "model": "DeepSeek-R1", "auth": "bearer"},
    "atoma": {"n": "Atoma", "cat": "infra", "method": "chat", "url": "https://api.atoma.network/v1/chat/completions", "model": "deepseek-ai/DeepSeek-R1", "auth": "bearer"},

    # ===== inference clouds / routers =====
    "openrouter": {"n": "OpenRouter", "cat": "infra", "method": "special", "prefix": ["sk-or-"]},
    "groq": {"n": "Groq", "cat": "infra", "method": "chat", "url": "https://api.groq.com/openai/v1/chat/completions", "model": "openai/gpt-oss-120b", "auth": "bearer", "prefix": ["gsk_"]},
    "cerebras": {"n": "Cerebras", "cat": "infra", "method": "chat", "url": "https://api.cerebras.ai/v1/chat/completions", "model": "gpt-oss-120b", "auth": "bearer", "prefix": ["csk-"]},
    "fireworks": {"n": "Fireworks", "cat": "infra", "method": "chat", "url": "https://api.fireworks.ai/inference/v1/chat/completions", "model": "accounts/fireworks/models/kimi-k2-instruct", "auth": "bearer", "prefix": ["fw_"]},
    "nvidia": {"n": "NVIDIA NIM", "cat": "infra", "method": "chat", "url": "https://integrate.api.nvidia.com/v1/chat/completions", "model": "deepseek-ai/deepseek-r1", "auth": "bearer", "prefix": ["nvapi-"]},
    "together": {"n": "Together AI", "cat": "infra", "method": "chat", "url": "https://api.together.xyz/v1/chat/completions", "model": "moonshotai/Kimi-K2-Instruct", "auth": "bearer"},
    "sambanova": {"n": "SambaNova", "cat": "infra", "method": "chat", "url": "https://api.sambanova.ai/v1/chat/completions", "model": "DeepSeek-V3.1", "auth": "bearer"},
    "deepinfra": {"n": "DeepInfra", "cat": "infra", "method": "get", "url": "https://api.deepinfra.com/v1/me?checklist=true", "model": "deepseek-ai/DeepSeek-V3", "auth": "bearer", "balance": _bal_deepinfra},
    "novita": {"n": "Novita", "cat": "infra", "method": "get", "url": "https://api.novita.ai/openapi/v1/billing/balance/detail", "model": "deepseek/deepseek-v3", "auth": "bearer", "balance": _bal_novita},
    "hyperbolic": {"n": "Hyperbolic", "cat": "infra", "method": "get", "url": "https://api.hyperbolic.xyz/v1/billing/get_current_balance", "model": "deepseek-ai/DeepSeek-V3", "auth": "bearer", "balance": _bal_hyperbolic},
    "nebius": {"n": "Nebius AI", "cat": "infra", "method": "chat", "url": "https://api.studio.nebius.com/v1/chat/completions", "model": "deepseek-ai/DeepSeek-V3-0324", "auth": "bearer"},
    "lambda": {"n": "Lambda", "cat": "infra", "method": "chat", "url": "https://api.lambda.ai/v1/chat/completions", "model": "deepseek-v3-0324", "auth": "bearer"},
    "featherless": {"n": "Featherless", "cat": "infra", "method": "chat", "url": "https://api.featherless.ai/v1/chat/completions", "model": "deepseek-ai/DeepSeek-V3.2", "auth": "bearer"},
    "siliconflow": {"n": "SiliconFlow", "cat": "infra", "method": "get", "url": "https://api.siliconflow.cn/v1/user/info", "model": "deepseek-ai/DeepSeek-V3", "auth": "bearer", "balance": _bal_siliconflow},
    "klusterai": {"n": "Kluster AI", "cat": "infra", "method": "chat", "url": "https://api.kluster.ai/v1/chat/completions", "model": "deepseek-ai/DeepSeek-V3", "auth": "bearer"},
    "inferencenet": {"n": "Inference.net", "cat": "infra", "method": "chat", "url": "https://api.inference.net/v1/chat/completions", "model": "deepseek/deepseek-v3", "auth": "bearer"},
    "aimlapi": {"n": "AI/ML API", "cat": "infra", "method": "chat", "url": "https://api.aimlapi.com/v1/chat/completions", "model": "gpt-5.5", "auth": "bearer"},
    "github": {"n": "GitHub Models", "cat": "infra", "method": "chat", "url": "https://models.github.ai/inference/chat/completions", "model": "openai/gpt-4.1", "auth": "bearer", "prefix": ["ghp_", "github_pat_", "gho_"]},
    "friendli": {"n": "FriendliAI", "cat": "infra", "method": "chat", "url": "https://api.friendli.ai/serverless/v1/chat/completions", "model": "deepseek-r1", "auth": "bearer", "prefix": ["flp_"]},
    "chutes": {"n": "Chutes", "cat": "infra", "method": "get", "url": "https://api.chutes.ai/users/me", "model": "deepseek-ai/DeepSeek-V3-0324", "auth": "bearer", "prefix": ["cpk_"], "balance": _bal_chutes},
    "vercel": {"n": "Vercel AI Gateway", "cat": "infra", "method": "get", "url": "https://ai-gateway.vercel.sh/v1/credits", "model": "-", "auth": "bearer", "prefix": ["vck_"], "balance": _bal_vercel},
    "volcengine": {"n": "Volcengine Ark", "cat": "infra", "method": "chat", "url": "https://ark.cn-beijing.volces.com/api/v3/chat/completions", "model": "doubao-seed-1-6-251015", "auth": "bearer"},
    "modelscope": {"n": "ModelScope", "cat": "infra", "method": "chat", "url": "https://api-inference.modelscope.cn/v1/chat/completions", "model": "Qwen/Qwen3-235B-A22B", "auth": "bearer"},
    "targon": {"n": "Targon", "cat": "infra", "method": "chat", "url": "https://api.targon.com/v1/chat/completions", "model": "deepseek-ai/DeepSeek-V3", "auth": "bearer"},
    "gmi": {"n": "GMI Cloud", "cat": "infra", "method": "chat", "url": "https://api.gmi-serving.com/v1/chat/completions", "model": "deepseek-ai/DeepSeek-V3", "auth": "bearer"},
    "scaleway": {"n": "Scaleway", "cat": "infra", "method": "chat", "url": "https://api.scaleway.ai/v1/chat/completions", "model": "deepseek-r1", "auth": "bearer"},
    "ovh": {"n": "OVHcloud AI", "cat": "infra", "method": "chat", "url": "https://oai.endpoints.kepler.ai.cloud.ovh.net/v1/chat/completions", "model": "DeepSeek-R1-Distill-Llama-70B", "auth": "bearer"},
    "requesty": {"n": "Requesty", "cat": "infra", "method": "chat", "url": "https://router.requesty.ai/v1/chat/completions", "model": "openai/gpt-4o", "auth": "bearer"},
    "glama": {"n": "Glama", "cat": "infra", "method": "chat", "url": "https://glama.ai/api/gateway/openai/v1/chat/completions", "model": "gpt-4o", "auth": "bearer"},
    "mancer": {"n": "Mancer", "cat": "infra", "method": "chat", "url": "https://neuro.mancer.tech/oai/v1/chat/completions", "model": "weaver", "auth": "bearer"},
    "arliai": {"n": "Arli AI", "cat": "infra", "method": "chat", "url": "https://api.arliai.com/v1/chat/completions", "model": "Meta-Llama-3.1-8B-Instruct", "auth": "bearer"},
    "avian": {"n": "Avian", "cat": "infra", "method": "chat", "url": "https://api.avian.io/v1/chat/completions", "model": "DeepSeek-R1", "auth": "bearer"},
    "netmind": {"n": "NetMind", "cat": "infra", "method": "chat", "url": "https://api.netmind.ai/inference-api/openai/v1/chat/completions", "model": "deepseek-ai/DeepSeek-V3", "auth": "bearer"},
    "clarifai": {"n": "Clarifai", "cat": "infra", "method": "chat", "url": "https://api.clarifai.com/v2/ext/openai/v1/chat/completions", "model": "gpt-oss-120b", "auth": "bearer"},

    # ===== embeddings / rerank =====
    "voyage": {"n": "Voyage AI", "cat": "embed", "method": "embed", "url": "https://api.voyageai.com/v1/embeddings", "model": "voyage-3-large", "auth": "bearer", "prefix": ["pa-"], "body": {"model": "voyage-3-large", "input": "hi"}},
    "jina": {"n": "Jina AI", "cat": "embed", "method": "special", "model": "jina-embeddings-v3", "prefix": ["jina_"]},
    "mixedbread": {"n": "Mixedbread", "cat": "embed", "method": "embed", "url": "https://api.mixedbread.com/v1/embeddings", "model": "mxbai-embed-large-v1", "auth": "bearer", "prefix": ["mxb_"], "body": {"model": "mxbai-embed-large-v1", "input": ["hi"]}},
    "nomic": {"n": "Nomic Atlas", "cat": "embed", "method": "get", "url": "https://api-atlas.nomic.ai/v1/user/", "model": "nomic-embed-text-v1.5", "auth": "bearer", "prefix": ["nk-"]},

    # ===== voice / audio =====
    "elevenlabs": {"n": "ElevenLabs", "cat": "voice", "method": "get", "url": "https://api.elevenlabs.io/v1/user/subscription", "model": "eleven_v3", "auth": "xi", "balance": _bal_elevenlabs},
    "deepgram": {"n": "Deepgram", "cat": "voice", "method": "special"},
    "assemblyai": {"n": "AssemblyAI", "cat": "voice", "method": "get", "url": "https://api.assemblyai.com/v2/account", "model": "universal", "auth": "raw"},
    "cartesia": {"n": "Cartesia", "cat": "voice", "method": "get", "url": "https://api.cartesia.ai/voices?limit=1", "model": "sonic-2", "auth": "cartesia", "prefix": ["sk_car_"]},
    "revai": {"n": "Rev AI", "cat": "voice", "method": "get", "url": "https://api.rev.ai/speechtotext/v1/account", "model": "-", "auth": "bearer", "balance": _bal_revai},
    "resemble": {"n": "Resemble AI", "cat": "voice", "method": "get", "url": "https://app.resemble.ai/api/v2/projects?page=1", "model": "-", "auth": "bearer"},
    "unrealspeech": {"n": "Unreal Speech", "cat": "voice", "method": "probe", "url": "https://api.v8.unrealspeech.com/stream", "model": "-", "auth": "bearer"},

    # ===== image =====
    "stability": {"n": "Stability AI", "cat": "image", "method": "special"},
    "leonardo": {"n": "Leonardo AI", "cat": "image", "method": "get", "url": "https://cloud.leonardo.ai/api/rest/v1/me", "model": "phoenix", "auth": "bearer", "balance": _bal_leonardo},
    "recraft": {"n": "Recraft", "cat": "image", "method": "get", "url": "https://external.api.recraft.ai/v1/users/me", "model": "recraftv3", "auth": "bearer", "balance": _bal_recraft},
    "bfl": {"n": "Black Forest Labs", "cat": "image", "method": "get", "url": "https://api.bfl.ai/v1/credits", "model": "flux-2-pro", "auth": "xkey", "balance": _bal_bfl},
    "ideogram": {"n": "Ideogram", "cat": "image", "method": "probe", "url": "https://api.ideogram.ai/v1/ideogram-v3/generate", "model": "ideogram-v3", "auth": "apikey"},
    "removebg": {"n": "remove.bg", "cat": "image", "method": "get", "url": "https://api.remove.bg/v1.0/account", "model": "-", "auth": "xapikey", "balance": _bal_removebg},
    "segmind": {"n": "Segmind", "cat": "image", "method": "get", "url": "https://api.segmind.com/v1/get-user-credits", "model": "-", "auth": "xapikey", "balance": _bal_segmind},
    "photoroom": {"n": "PhotoRoom", "cat": "image", "method": "get", "url": "https://image-api.photoroom.com/v2/account", "model": "-", "auth": "xapikey", "balance": _bal_photoroom},
    "clipdrop": {"n": "Clipdrop", "cat": "image", "method": "special"},
    "deepai": {"n": "DeepAI", "cat": "image", "method": "probe", "url": "https://api.deepai.org/api/text2img", "model": "-", "auth": "apikey"},

    # ===== video =====
    "runwayml": {"n": "RunwayML", "cat": "video", "method": "get", "url": "https://api.dev.runwayml.com/v1/organization", "model": "gen-4", "auth": "runway", "prefix": ["key_"], "balance": _bal_runway},
    "luma": {"n": "Luma Dream Machine", "cat": "video", "method": "get", "url": "https://api.lumalabs.ai/dream-machine/v1/credits", "model": "ray-3", "auth": "bearer", "prefix": ["luma-"], "balance": _bal_luma},
    "heygen": {"n": "HeyGen", "cat": "video", "method": "get", "url": "https://api.heygen.com/v2/user/remaining_quota", "model": "-", "auth": "xapikey", "balance": _bal_heygen},
    "synthesia": {"n": "Synthesia", "cat": "video", "method": "get", "url": "https://api.synthesia.io/v2/videos?limit=1", "model": "-", "auth": "raw"},
    "tavus": {"n": "Tavus", "cat": "video", "method": "get", "url": "https://tavusapi.com/v2/replicas?limit=1", "model": "-", "auth": "xapikey"},
    "vidu": {"n": "Vidu", "cat": "video", "method": "get", "url": "https://api.vidu.com/ent/v2/credits", "model": "-", "auth": "token", "balance": _bal_vidu},

    # ===== generic account checks (kept) =====
    "replicate": {"n": "Replicate", "cat": "infra", "method": "get", "url": "https://api.replicate.com/v1/account", "model": "-", "auth": "bearer", "prefix": ["r8_"], "balance": _info_replicate},
    "huggingface": {"n": "Hugging Face", "cat": "infra", "method": "get", "url": "https://huggingface.co/api/whoami-v2", "model": "-", "auth": "bearer", "prefix": ["hf_"], "balance": _info_hf},
}

# ---- listing-only providers (shown in .kprov, need special creds to check) ----
_LIST = {
    # chat / infra
    "cloudflare": ("Cloudflare Workers AI", "infra"), "azureopenai": ("Azure OpenAI", "infra"),
    "vertexai": ("Google Vertex AI", "infra"), "bedrock": ("AWS Bedrock", "infra"),
    "watsonx": ("IBM watsonx", "infra"), "databricks": ("Databricks", "infra"),
    "snowflake": ("Snowflake Cortex", "infra"), "sensenova": ("SenseTime SenseNova", "chat"),
    "alephalpha": ("Aleph Alpha", "chat"), "nlpcloud": ("NLP Cloud", "chat"),
    "predibase": ("Predibase", "infra"), "baseten": ("Baseten", "infra"),
    "runpod": ("RunPod", "infra"), "lepton": ("Lepton AI", "infra"),
    "crusoe": ("Crusoe", "infra"), "koyeb": ("Koyeb", "infra"), "gcore": ("Gcore", "infra"),
    "hyperstack": ("Hyperstack", "infra"), "you": ("You.com", "chat"),
    "portkey": ("Portkey", "infra"), "helicone": ("Helicone", "infra"),
    "martian": ("Martian", "infra"), "edenai": ("Eden AI", "infra"),
    "openpipe": ("OpenPipe", "infra"), "parasail": ("Parasail", "infra"),
    "anyscale": ("Anyscale", "infra"), "kuaishou": ("Kuaishou KwaiYii", "chat"),
    "360ai": ("360 Zhinao", "chat"), "doubao": ("ByteDance Doubao", "chat"),
    # image
    "fal": ("fal.ai", "image"), "civitai": ("Civitai", "image"),
    "freepik": ("Freepik / Mystic", "image"), "scenario": ("Scenario", "image"),
    "picsart": ("Picsart", "image"), "tensorart": ("Tensor.art", "image"),
    "playground": ("Playground AI", "image"), "krea": ("Krea", "image"),
    "magnific": ("Magnific", "image"), "bria": ("Bria", "image"),
    "getimg": ("Getimg.ai", "image"), "novelai": ("NovelAI", "image"),
    "prodia": ("Prodia", "image"), "dezgo": ("Dezgo", "image"),
    "modelslab": ("ModelsLab", "image"), "starryai": ("StarryAI", "image"),
    "adobefirefly": ("Adobe Firefly", "image"), "vanceai": ("Vance AI", "image"),
    "lightricks": ("Lightricks LTX", "image"), "midjourney": ("Midjourney", "image"),
    "dalle": ("OpenAI DALL-E 3", "image"), "imagen": ("Google Imagen", "image"),
    # video
    "pika": ("Pika", "video"), "kling": ("Kling", "video"),
    "hailuo": ("Hailuo (MiniMax)", "video"), "haiper": ("Haiper", "video"),
    "did": ("D-ID", "video"), "hedra": ("Hedra", "video"),
    "captions": ("Captions", "video"), "veo": ("Google Veo", "video"),
    "sora": ("OpenAI Sora", "video"), "higgsfield": ("Higgsfield", "video"),
    "viggle": ("Viggle", "video"), "deepbrain": ("DeepBrain AI", "video"),
    "argil": ("Argil", "video"), "colossyan": ("Colossyan", "video"),
    "genmo": ("Genmo Mochi", "video"), "wan": ("Alibaba Wan", "video"),
    "seedance": ("ByteDance Seedance", "video"), "pixverse": ("PixVerse", "video"),
    "domo": ("Domo AI", "video"), "pollo": ("Pollo AI", "video"),
    # voice
    "playht": ("PlayHT", "voice"), "hume": ("Hume AI", "voice"),
    "gladia": ("Gladia", "voice"), "fishaudio": ("Fish Audio", "voice"),
    "lmnt": ("LMNT", "voice"), "murf": ("Murf", "voice"),
    "rime": ("Rime", "voice"), "speechify": ("Speechify", "voice"),
    "neets": ("Neets", "voice"), "cambai": ("Camb.ai", "voice"),
    "wellsaid": ("WellSaid", "voice"), "speechmatics": ("Speechmatics", "voice"),
    "sesame": ("Sesame", "voice"), "kits": ("Kits AI", "voice"),
    "narakeet": ("Narakeet", "voice"), "voicemaker": ("Voicemaker", "voice"),
    "topmediai": ("TopMediai", "voice"), "whisper": ("OpenAI Whisper", "voice"),
    "azurespeech": ("Azure Speech", "voice"), "googlestt": ("Google STT", "voice"),
    # music
    "suno": ("Suno", "music"), "udio": ("Udio", "music"),
    "mubert": ("Mubert", "music"), "beatoven": ("Beatoven", "music"),
    "loudly": ("Loudly", "music"), "sonauto": ("Sonauto", "music"),
    "lalal": ("Lalal.ai", "music"), "riffusion": ("Riffusion", "music"),
    "stableaudio": ("Stability Audio", "music"), "elevenmusic": ("ElevenLabs Music", "music"),
}
for _pid, (_n, _c) in _LIST.items():
    SPECS.setdefault(_pid, {"n": _n, "cat": _c})

# ---- extended catalog (listing-only) ----
_LIST2 = {
    # chat / LLM labs
    "exaone": ("LG EXAONE", "chat"), "liquid": ("Liquid AI", "chat"), "sarvam": ("Sarvam AI", "chat"),
    "arcee": ("Arcee AI", "chat"), "olmo": ("AllenAI OLMo", "chat"), "internlm": ("InternLM", "chat"),
    "falcon": ("Falcon (TII)", "chat"), "jais": ("Jais (MBZUAI)", "chat"), "sealion": ("SEA-LION", "chat"),
    "yandexgpt": ("YandexGPT", "chat"), "gigachat": ("GigaChat (Sber)", "chat"), "tbank": ("T-Bank T-Pro", "chat"),
    "granite": ("IBM Granite", "chat"), "arctic": ("Snowflake Arctic", "chat"), "dbrx": ("Databricks DBRX", "chat"),
    "phi": ("Microsoft Phi", "chat"), "nemotron": ("NVIDIA Nemotron", "chat"), "cogito": ("Deep Cogito", "chat"),
    "goodfire": ("Goodfire Ember", "chat"), "llm360": ("LLM360 K2", "chat"), "minicpm": ("MiniCPM (ModelBest)", "chat"),
    "pangu": ("Pangu (Huawei)", "chat"), "telechat": ("TeleChat", "chat"), "skywork": ("Skywork", "chat"),
    "inflection": ("Inflection Pi", "chat"), "characterai": ("Character.AI", "chat"), "poe": ("Poe (Quora)", "chat"),
    "huggingchat": ("HuggingChat", "chat"), "tng": ("TNG DeepSeek R1T", "chat"), "erniebot": ("ERNIE Bot", "chat"),
    # inference clouds / gateways
    "modal": ("Modal", "infra"), "beam": ("Beam Cloud", "infra"), "cerebrium": ("Cerebrium", "infra"),
    "salad": ("Salad Cloud", "infra"), "vastai": ("Vast.ai", "infra"), "tensordock": ("TensorDock", "infra"),
    "datacrunch": ("DataCrunch", "infra"), "paperspace": ("Paperspace", "infra"), "coreweave": ("CoreWeave", "infra"),
    "fluidstack": ("FluidStack", "infra"), "latitude": ("Latitude.sh", "infra"), "voltagepark": ("Voltage Park", "infra"),
    "genesiscloud": ("Genesis Cloud", "infra"), "lamini": ("Lamini", "infra"), "notdiamond": ("Not Diamond", "infra"),
    "kong": ("Kong AI Gateway", "infra"), "litellm": ("LiteLLM", "infra"), "keywordsai": ("Keywords AI", "infra"),
    "langdock": ("Langdock", "infra"), "braintrust": ("Braintrust", "infra"), "cloudrift": ("Cloudrift", "infra"),
    "hyperbee": ("Hyperbee", "infra"), "apipie": ("APIpie", "infra"), "shuttleai": ("Shuttle AI", "infra"),
    "electronhub": ("ElectronHub", "infra"), "nagaai": ("NagaAI", "infra"), "zukijourney": ("Zukijourney", "infra"),
    "cablyai": ("CablyAI", "infra"), "vsegpt": ("VseGPT", "infra"), "bothub": ("BotHub", "infra"),
    "gptunnel": ("GPTunnel", "infra"), "aitunnel": ("AITUNNEL", "infra"), "proxyapi": ("ProxyAPI", "infra"),
    "octoai": ("OctoAI", "infra"), "mysticai": ("Mystic.ai", "infra"), "pipelineai": ("Pipeline AI", "infra"),
    # image
    "runware": ("Runware", "image"), "wavespeed": ("WaveSpeed AI", "image"), "reve": ("Reve", "image"),
    "photai": ("Phot.AI", "image"), "pixelcut": ("Pixelcut", "image"), "claid": ("Claid.ai", "image"),
    "pebblely": ("Pebblely", "image"), "vyro": ("Imagine (Vyro)", "image"), "magespace": ("Mage.space", "image"),
    "astria": ("Astria", "image"), "generatedphotos": ("Generated Photos", "image"), "letsenhance": ("Let's Enhance", "image"),
    "hotpot": ("Hotpot.ai", "image"), "stockimg": ("Stockimg.ai", "image"), "neurallove": ("Neural.love", "image"),
    "cutout": ("Cutout.pro", "image"), "goenhance": ("GoEnhance", "image"), "comfyicu": ("ComfyICU", "image"),
    "runcomfy": ("RunComfy", "image"), "rundiffusion": ("RunDiffusion", "image"), "thinkdiffusion": ("ThinkDiffusion", "image"),
    "seedream": ("Seedream (ByteDance)", "image"), "qwenimage": ("Qwen-Image", "image"), "hunyuanimage": ("Hunyuan Image", "image"),
    "nanobanana": ("Nano Banana", "image"), "topaz": ("Topaz Labs", "image"), "stablecog": ("Stablecog", "image"),
    "fluxpro": ("Flux Kontext", "image"), "krea2": ("Krea Image", "image"),
    # video
    "cogvideo": ("CogVideo (Zhipu)", "video"), "hunyuanvideo": ("Hunyuan Video", "video"), "marey": ("Marey (Moonvalley)", "video"),
    "ltx": ("LTX (Lightricks)", "video"), "kreavideo": ("Krea Video", "video"), "elai": ("Elai.io", "video"),
    "steveai": ("Steve AI", "video"), "fliki": ("Fliki", "video"), "invideo": ("InVideo", "video"),
    "pictory": ("Pictory", "video"), "veed": ("VEED", "video"), "capcut": ("CapCut / Pippit", "video"),
    "hourone": ("Hour One", "video"), "yepic": ("Yepic AI", "video"), "rephrase": ("Rephrase.ai", "video"),
    "krikey": ("Krikey AI", "video"), "deepmotion": ("DeepMotion", "video"), "moveai": ("Move AI", "video"),
    "wonderdynamics": ("Wonder Dynamics", "video"), "vozo": ("Vozo", "video"), "sieve": ("Sieve", "video"),
    "decohere": ("Decohere", "video"), "dreamina": ("Dreamina (CapCut)", "video"), "lumalabs2": ("Luma Ray", "video"),
    # voice / audio
    "polly": ("Amazon Polly", "voice"), "watsontts": ("IBM Watson Speech", "voice"), "inworld": ("Inworld AI", "voice"),
    "smallestai": ("Smallest.ai", "voice"), "vapi": ("Vapi", "voice"), "retell": ("Retell AI", "voice"),
    "bland": ("Bland AI", "voice"), "vocode": ("Vocode", "voice"), "deepdub": ("Deepdub", "voice"),
    "papercup": ("Papercup", "voice"), "respeecher": ("Respeecher", "voice"), "replicastudios": ("Replica Studios", "voice"),
    "lovo": ("LOVO Genny", "voice"), "listnr": ("Listnr", "voice"), "podcastle": ("Podcastle", "voice"),
    "descript": ("Descript", "voice"), "typecast": ("Typecast", "voice"), "fakeyou": ("FakeYou", "voice"),
    "voicemod": ("Voicemod", "voice"), "speechki": ("Speechki", "voice"), "soniox": ("Soniox", "voice"),
    "otter": ("Otter.ai", "voice"), "fireflies": ("Fireflies.ai", "voice"), "sonix": ("Sonix", "voice"),
    "happyscribe": ("Happy Scribe", "voice"), "picovoice": ("Picovoice", "voice"), "playai": ("PlayAI", "voice"),
    # music
    "aiva": ("AIVA", "music"), "soundraw": ("Soundraw", "music"), "boomy": ("Boomy", "music"),
    "soundful": ("Soundful", "music"), "splash": ("Splash", "music"), "aimi": ("Aimi", "music"),
    "musicfy": ("Musicfy", "music"), "jenmusic": ("Jen (JenMusic)", "music"), "lemonaide": ("Lemonaide", "music"),
    "moises": ("Moises", "music"), "audoai": ("Audo AI", "music"), "cassetteai": ("Cassette AI", "music"),
    "musicgen": ("MusicGen (Meta)", "music"), "musicfx": ("MusicFX (Google)", "music"), "songr": ("SongR", "music"),
    # embeddings / rerank
    "pinecone": ("Pinecone Inference", "embed"), "contextual": ("Contextual AI", "embed"), "zeroentropy": ("ZeroEntropy", "embed"),
    "marqo": ("Marqo", "embed"), "vectara": ("Vectara", "embed"), "superlinked": ("Superlinked", "embed"),
    "baai": ("BAAI BGE", "embed"),
    # search / retrieval
    "exa": ("Exa", "search"), "tavily": ("Tavily", "search"), "serper": ("Serper", "search"),
    "serpapi": ("SerpAPI", "search"), "brave": ("Brave Search", "search"), "linkup": ("Linkup", "search"),
    "kagi": ("Kagi", "search"), "valyu": ("Valyu", "search"), "parallel": ("Parallel AI", "search"),
    "jinasearch": ("Jina DeepSearch", "search"),
    # OCR / documents / vision
    "mistralocr": ("Mistral OCR", "doc"), "llamaparse": ("LlamaParse", "doc"), "unstructured": ("Unstructured.io", "doc"),
    "mathpix": ("Mathpix", "doc"), "nanonets": ("Nanonets", "doc"), "reducto": ("Reducto", "doc"),
    "documentai": ("Google Document AI", "doc"), "textract": ("AWS Textract", "doc"), "azuredi": ("Azure Doc Intelligence", "doc"),
    "klippa": ("Klippa", "doc"), "docsumo": ("Docsumo", "doc"), "roboflow": ("Roboflow", "doc"),
    "landingai": ("Landing AI", "doc"), "moondream": ("Moondream", "doc"), "chunkr": ("Chunkr", "doc"),
    "omniai": ("OmniAI", "doc"), "datalab": ("Datalab Marker", "doc"), "extend": ("Extend", "doc"),
    # agent tools / infra
    "firecrawl": ("Firecrawl", "tools"), "scrapingbee": ("ScrapingBee", "tools"), "brightdata": ("Bright Data", "tools"),
    "scrapingdog": ("ScrapingDog", "tools"), "zenrows": ("ZenRows", "tools"), "apify": ("Apify", "tools"),
    "browserbase": ("Browserbase", "tools"), "browserless": ("Browserless", "tools"), "steel": ("Steel.dev", "tools"),
    "hyperbrowser": ("Hyperbrowser", "tools"), "e2b": ("E2B", "tools"), "langsmith": ("LangSmith", "tools"),
    "langfuse": ("Langfuse", "tools"), "phoenix": ("Arize Phoenix", "tools"), "composio": ("Composio", "tools"),
    "llamacloud": ("LlamaCloud", "tools"), "agentops": ("AgentOps", "tools"), "weave": ("W&B Weave", "tools"),
    "opik": ("Comet Opik", "tools"), "daily": ("Daily Pipecat", "tools"),
}
for _pid, (_n, _c) in _LIST2.items():
    SPECS.setdefault(_pid, {"n": _n, "cat": _c})

NAMES = {pid: s["n"] for pid, s in SPECS.items()}
CATS = ("chat", "infra", "image", "video", "voice", "music", "embed", "search", "doc", "tools")

PREFIX_MAP = []
for _pid, _s in SPECS.items():
    for _p in _s.get("prefix", []):
        PREFIX_MAP.append((_p, _pid))
PREFIX_MAP.sort(key=lambda x: -len(x[0]))

# probe groups (validatable only)
SK_DASH = ["openai", "deepseek", "moonshot", "qwen", "stability"]
SK_UNDER = ["elevenlabs", "novita"]
JWT_GROUP = ["minimax", "nebius", "hyperbolic"]
DOT_GROUP = ["zhipu", "minimax"]
LOOSE = [
    "mistral", "cohere", "together", "sambanova", "ai21", "deepinfra", "reka",
    "writer", "aimlapi", "lambda", "stepfun", "baichuan", "featherless",
    "siliconflow", "klusterai", "inferencenet", "deepgram", "assemblyai",
    "leonardo", "recraft", "heygen", "synthesia",
]
# extra candidates probed only when config "deep" is on
DEEP_EXTRA = [
    "yi", "hunyuan", "qianfan", "spark", "volcengine", "modelscope", "targon",
    "gmi", "scaleway", "ovh", "requesty", "glama", "mancer",
    "arliai", "avian", "netmind", "clarifai", "removebg", "revai", "resemble",
    "tavus", "segmind", "photoroom", "clipdrop", "deepai", "vidu", "unrealspeech",
    "bfl", "ideogram", "nscale", "nous", "twoai", "krutrim", "atoma",
]

AUTH_FAIL = ("invalid api key", "invalid_api_key", "incorrect api key", "unauthorized",
             "authentication", "api key not valid", "invalid token", "could not validate")
QUOTA = ("insufficient", "quota", "exceeded your current", "billing", "payment required",
         "not enough", "balance", "no credit", "out of credit", "arrears")
REGION = ("unsupported_country", "country", "region", "territory", "not available in your")

_UUID = re.compile(r"[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}")
_FALKEY = re.compile(r"[0-9a-fA-F]{8,}:[0-9a-zA-Z]{16,}")
_DOTKEY = re.compile(r"[0-9a-zA-Z]{16,}\.[A-Za-z0-9]{8,}")
_TOKEN = re.compile(r"[A-Za-z0-9_\-]{20,}")


def _auth_headers(spec, key):
    a = spec.get("auth", "bearer")
    h = {}
    if a == "bearer":
        h["Authorization"] = "Bearer " + key
    elif a == "anthropic":
        h["x-api-key"] = key
        h["anthropic-version"] = "2023-06-01"
    elif a == "xi":
        h["xi-api-key"] = key
    elif a == "token":
        h["Authorization"] = "Token " + key
    elif a == "raw":
        h["Authorization"] = key
    elif a == "xkey":
        h["x-key"] = key
    elif a == "xapikey":
        h["X-Api-Key"] = key
    elif a == "apikey":
        h["Api-Key"] = key
    elif a == "cartesia":
        h["Authorization"] = "Bearer " + key
        h["Cartesia-Version"] = "2024-11-13"
    elif a == "runway":
        h["Authorization"] = "Bearer " + key
        h["X-Runway-Version"] = "2024-11-06"
    if spec.get("method") in ("chat", "embed", "probe"):
        h["Content-Type"] = "application/json"
    return h


def _interpret(status, text):
    low = (text or "").lower()
    if status == 200:
        return ("valid", None)
    if status == 401:
        return ("invalid", None)
    if status == 403:
        return ("forbidden", None) if any(m in low for m in REGION) else ("invalid", None)
    if status == 402:
        return ("no_balance", None)
    if status == 429:
        return ("no_balance", None) if any(m in low for m in QUOTA) else ("rate_limited", None)
    if status in (400, 404, 422):
        if any(m in low for m in ("invalid api key", "invalid_api_key", "incorrect api key", "api key not valid", "unauthorized", "authentication")):
            return ("invalid", None)
        if any(m in low for m in QUOTA):
            return ("no_balance", None)
        return ("valid", "model")
    if status == 529:
        return ("valid", "overloaded")
    if any(m in low for m in AUTH_FAIL):
        return ("invalid", None)
    return ("error", "http %s" % status)


def _interpret_get(status, text):
    low = (text or "").lower()
    if status == 200:
        return ("valid", None)
    if status in (401, 407):
        return ("invalid", None)
    if status == 403:
        return ("forbidden", None) if any(m in low for m in REGION) else ("invalid", None)
    if status == 402:
        return ("no_balance", None)
    if status == 429:
        return ("rate_limited", None)
    if any(m in low for m in AUTH_FAIL):
        return ("invalid", None)
    return ("error", "http %s" % status)


def _interpret_probe(status, text):
    low = (text or "").lower()
    if status == 401:
        return ("invalid", None)
    if status == 403:
        return ("forbidden", None) if any(m in low for m in REGION) else ("invalid", None)
    if status == 402:
        return ("no_balance", None)
    if status == 429:
        return ("no_balance", None) if any(m in low for m in QUOTA) else ("rate_limited", None)
    if status in (200, 400, 422):
        if any(m in low for m in ("invalid api key", "unauthorized", "api key not valid")):
            return ("invalid", None)
        return ("valid", None)
    return ("error", "http %s" % status)


def _R(verdict, balance=None, model=None, detail=None, info=None):
    return {"verdict": verdict, "balance": balance, "model": model, "detail": detail, "info": info}


# Tier mappings: RPM (int) → tier label
_ANTHROPIC_TIER_MAP = {50: "Tier 1", 1_000: "Tier 2", 2_000: "Tier 3", 4_000: "Tier 4"}
_OPENAI_TIER_MAP    = {3: "Free",    500: "Tier 1",   5_000: "Tier 2",  10_000: "Tier 4",
                       15_000: "Tier 5"}
_GROQ_TIER_MAP      = {30: "Free",   300: "Developer"}
_SAMBANOVA_TIER_MAP = {20: "Free",   60: "Developer", 240: "Developer"}
_CEREBRAS_TIER_MAP  = {30: "Free Trial", 1_000: "Developer"}


def _rpm_to_tier(rpm_val, tier_map, fallback_fn=None):
    try:
        r = int(rpm_val)
    except (TypeError, ValueError):
        return None
    if r in tier_map:
        return tier_map[r]
    if fallback_fn:
        return fallback_fn(r)
    return None


def _rate_info(headers, pid, resp_text, verdict):
    """Map rate-limit response headers to tier label. Shows Tier N, not raw limits."""
    if verdict not in ("valid", "no_balance", "rate_limited"):
        return None
    parts = []

    if pid == "anthropic":
        req = headers.get("anthropic-ratelimit-requests-limit")
        tier = _rpm_to_tier(req, _ANTHROPIC_TIER_MAP,
                            lambda r: ("Tier 1" if r <= 50 else
                                       "Tier 2" if r <= 1_000 else
                                       "Tier 3" if r <= 2_000 else "Tier 4"))
        if tier:
            parts.append(tier)
        # service_tier from body (Priority Tier accounts only)
        if resp_text:
            try:
                st = json.loads(resp_text).get("usage", {}).get("service_tier")
                if st and st != "standard":
                    parts.append(st)
            except Exception:  # noqa: BLE001
                pass

    elif pid == "openai":
        req = headers.get("x-ratelimit-limit-requests")
        tier = _rpm_to_tier(req, _OPENAI_TIER_MAP,
                            lambda r: ("Free"   if r <= 3    else
                                       "Tier 1" if r <= 500  else
                                       "Tier 2" if r <= 5_000 else
                                       "Tier 4" if r <= 10_000 else "Tier 5"))
        if tier:
            parts.append(tier)

    elif pid == "groq":
        req = headers.get("x-ratelimit-limit-requests")
        tier = _rpm_to_tier(req, _GROQ_TIER_MAP,
                            lambda r: "Free" if r <= 30 else "Developer")
        if tier:
            parts.append(tier)

    elif pid == "cerebras":
        req = headers.get("x-ratelimit-limit-requests-day")
        tier = _rpm_to_tier(req, _CEREBRAS_TIER_MAP,
                            lambda r: "Free Trial" if r <= 30 else "Developer")
        if tier:
            parts.append(tier)

    elif pid == "sambanova":
        req = headers.get("x-ratelimit-limit-requests")
        tier = _rpm_to_tier(req, _SAMBANOVA_TIER_MAP,
                            lambda r: "Free" if r <= 20 else "Developer")
        if tier:
            parts.append(tier)

    elif pid == "xai":
        req = headers.get("x-ratelimit-limit-requests")
        if req:
            try:
                r = int(req)
                tier = ("Tier 0" if r <= 60   else
                        "Tier 1" if r <= 500  else
                        "Tier 2" if r <= 2_000 else
                        "Tier 3" if r <= 8_000 else "Tier 4")
                parts.append(tier)
            except (TypeError, ValueError):
                pass

    return " · ".join(parts) if parts else None


async def _chat(session, key, spec, timeout, pid=None):
    payload = {"model": spec["model"], "messages": [{"role": "user", "content": "hi"}], "max_tokens": 1}
    try:
        async with session.post(spec["url"], json=payload, headers=_auth_headers(spec, key),
                                timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            text = await r.text()
            v, d = _interpret(r.status, text)
            info = _rate_info(r.headers, pid or "", text, v)
            return _R(v, None, spec["model"], d, info)
    except asyncio.TimeoutError:
        return _R("error", None, spec.get("model"), "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, spec.get("model"), str(e)[:80])


async def _embed(session, key, spec, timeout):
    try:
        async with session.post(spec["url"], json=spec["body"], headers=_auth_headers(spec, key),
                                timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            v, d = _interpret(r.status, await r.text())
            return _R(v, None, spec["model"], d)
    except asyncio.TimeoutError:
        return _R("error", None, spec.get("model"), "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, spec.get("model"), str(e)[:80])


async def _probe(session, key, spec, timeout):
    try:
        async with session.post(spec["url"], json={}, headers=_auth_headers(spec, key),
                                timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            v, d = _interpret_probe(r.status, await r.text())
            return _R(v, None, spec.get("model"), d)
    except asyncio.TimeoutError:
        return _R("error", None, spec.get("model"), "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, spec.get("model"), str(e)[:80])


async def _get(session, key, spec, timeout):
    try:
        async with session.get(spec["url"], headers=_auth_headers(spec, key),
                               timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            text = await r.text()
            v, d = _interpret_get(r.status, text)
            bal = None
            info = None
            if v == "valid" and spec.get("balance"):
                try:
                    result = spec["balance"](json.loads(text))
                    if len(result) == 3:
                        bv, bal, info = result
                    else:
                        bv, bal = result
                    if bv:
                        v = bv
                except Exception:  # noqa: BLE001
                    bal = None
            return _R(v, bal, spec.get("model"), d, info)
    except asyncio.TimeoutError:
        return _R("error", None, spec.get("model"), "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, spec.get("model"), str(e)[:80])


async def _deepseek(session, key, timeout):
    try:
        async with session.get("https://api.deepseek.com/user/balance",
                               headers={"Authorization": "Bearer " + key},
                               timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            if r.status == 200:
                d = await r.json(content_type=None)
                infos = d.get("balance_infos") or []
                bal = "%s %s" % (infos[0].get("total_balance"), infos[0].get("currency")) if infos else None
                return _R("valid" if d.get("is_available") else "no_balance", bal, "deepseek-v4-pro")
            v, dt = _interpret_get(r.status, await r.text())
            return _R(v, None, "deepseek-v4-pro", dt)
    except asyncio.TimeoutError:
        return _R("error", None, "deepseek-v4-pro", "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, "deepseek-v4-pro", str(e)[:80])


async def _openrouter(session, key, timeout):
    try:
        async with session.get("https://openrouter.ai/api/v1/key",
                               headers={"Authorization": "Bearer " + key},
                               timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            if r.status == 200:
                d = (await r.json(content_type=None)).get("data", {})
                limit, usage = d.get("limit"), d.get("usage") or 0
                rem = d.get("limit_remaining")
                if rem is None and limit is not None:
                    rem = limit - usage
                bal, v = None, "valid"
                if rem is not None:
                    bal = "$%.2f" % rem
                    if rem <= 0:
                        v = "no_balance"
                info_parts = []
                if d.get("label"):
                    info_parts.append(str(d["label"]))
                if d.get("is_free_tier"):
                    info_parts.append("free tier")
                return _R(v, bal, "openrouter/auto", info=" · ".join(info_parts) or None)
            v, dt = _interpret_get(r.status, await r.text())
            return _R(v, None, "openrouter/auto", dt)
    except asyncio.TimeoutError:
        return _R("error", None, "openrouter/auto", "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, "openrouter/auto", str(e)[:80])


async def _stability(session, key, timeout):
    try:
        async with session.get("https://api.stability.ai/v1/user/balance",
                               headers={"Authorization": "Bearer " + key, "Accept": "application/json"},
                               timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            if r.status == 200:
                c = (await r.json(content_type=None)).get("credits")
                v = "valid" if (c is None or c > 0) else "no_balance"
                return _R(v, None if c is None else "%s credits" % round(c, 2), "stable-image-ultra")
            v, dt = _interpret_get(r.status, await r.text())
            return _R(v, None, "stable-image-ultra", dt)
    except asyncio.TimeoutError:
        return _R("error", None, "stable-image-ultra", "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, "stable-image-ultra", str(e)[:80])


async def _google(session, key, timeout):
    url = "https://generativelanguage.googleapis.com/v1beta/models/gemini-3.1-pro:generateContent?key=" + key
    body = {"contents": [{"parts": [{"text": "hi"}]}], "generationConfig": {"maxOutputTokens": 1}}
    try:
        async with session.post(url, json=body, headers={"Content-Type": "application/json"},
                                timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            v, d = _interpret(r.status, await r.text())
            return _R(v, None, "gemini-3.1-pro", d)
    except asyncio.TimeoutError:
        return _R("error", None, "gemini-3.1-pro", "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, "gemini-3.1-pro", str(e)[:80])


async def _minimax(session, key, timeout):
    body = {"model": "MiniMax-Text-01", "messages": [{"role": "user", "content": "hi"}], "max_tokens": 1}
    try:
        async with session.post("https://api.minimaxi.com/v1/text/chatcompletion_v2", json=body,
                                headers={"Authorization": "Bearer " + key, "Content-Type": "application/json"},
                                timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            if r.status == 200:
                code = ((await r.json(content_type=None)).get("base_resp") or {}).get("status_code", 0)
                m = {0: "valid", 1004: "invalid", 1008: "no_balance", 1002: "rate_limited", 1039: "rate_limited"}
                return _R(m.get(code, "valid"), None, "MiniMax-Text-01", "code %s" % code)
            v, d = _interpret(r.status, await r.text())
            return _R(v, None, "MiniMax-Text-01", d)
    except asyncio.TimeoutError:
        return _R("error", None, "MiniMax-Text-01", "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, "MiniMax-Text-01", str(e)[:80])


async def _jina(session, key, timeout):
    url = "https://embeddings-dashboard-api.jina.ai/api/v1/api_key/user?api_key=" + key
    try:
        async with session.get(url, timeout=aiohttp.ClientTimeout(total=timeout)) as r:
            if r.status == 200:
                w = (await r.json(content_type=None)).get("wallet") or {}
                tot = (w.get("total_balance") or 0) + (w.get("trial_balance") or 0)
                bal = "%s tokens" % tot if w else None
                return _R("no_balance" if (w and tot <= 0) else "valid", bal, "jina-embeddings-v3")
            v, d = _interpret_get(r.status, await r.text())
            return _R(v, None, "jina-embeddings-v3", d)
    except asyncio.TimeoutError:
        return _R("error", None, "jina-embeddings-v3", "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, "jina-embeddings-v3", str(e)[:80])


async def _cohere_check(session, key, timeout):
    try:
        async with session.post(
            "https://api.cohere.com/v1/check-api-key",
            json={},
            headers={"Authorization": "Bearer " + key, "Content-Type": "application/json"},
            timeout=aiohttp.ClientTimeout(total=timeout),
        ) as r:
            if r.status == 200:
                d = await r.json(content_type=None)
                if d.get("valid"):
                    org = d.get("organization_id") or ""
                    return _R("valid", None, "command-a-03-2025", info=("org: %s" % org) if org else None)
                return _R("invalid", None, "command-a-03-2025")
            v, dt = _interpret_get(r.status, await r.text())
            return _R(v, None, "command-a-03-2025", dt)
    except asyncio.TimeoutError:
        return _R("error", None, "command-a-03-2025", "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, "command-a-03-2025", str(e)[:80])


async def _deepgram_check(session, key, timeout):
    try:
        async with session.get(
            "https://api.deepgram.com/v1/projects",
            headers={"Authorization": "Token " + key},
            timeout=aiohttp.ClientTimeout(total=timeout),
        ) as r:
            if r.status != 200:
                v, dt = _interpret_get(r.status, await r.text())
                return _R(v, None, "nova-3", dt)
            d = await r.json(content_type=None)
            projects = d.get("projects") or []
            if not projects:
                return _R("valid", None, "nova-3")
            proj_name = projects[0].get("name") or ""
            pid = projects[0].get("project_id")
        if pid:
            async with session.get(
                "https://api.deepgram.com/v1/projects/%s/balances" % pid,
                headers={"Authorization": "Token " + key},
                timeout=aiohttp.ClientTimeout(total=timeout),
            ) as r2:
                if r2.status == 200:
                    bals = (await r2.json(content_type=None)).get("balances") or []
                    if bals:
                        amt = bals[0].get("amount")
                        units = str(bals[0].get("units", "")).upper()
                        bal = "%s %s" % (amt, units) if amt is not None else None
                        v = "no_balance" if (amt is not None and amt <= 0) else "valid"
                        return _R(v, bal, "nova-3", info=proj_name or None)
        return _R("valid", None, "nova-3", info=proj_name or None)
    except asyncio.TimeoutError:
        return _R("error", None, "nova-3", "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, "nova-3", str(e)[:80])


async def _clipdrop_check(session, key, timeout):
    try:
        async with session.post(
            "https://clipdrop-api.co/text-to-image/v1",
            data={},
            headers={"x-api-key": key},
            timeout=aiohttp.ClientTimeout(total=timeout),
        ) as r:
            cr = r.headers.get("x-remaining-credits")
            if r.status == 401:
                return _R("invalid", None, "-")
            if r.status in (200, 400, 422):
                bal = "%s credits" % cr if cr else None
                try:
                    v = "no_balance" if (cr and int(cr) <= 0) else "valid"
                except (ValueError, TypeError):
                    v = "valid"
                return _R(v, bal, "-")
            v, dt = _interpret_probe(r.status, await r.text())
            return _R(v, "%s credits" % cr if cr else None, "-", dt)
    except asyncio.TimeoutError:
        return _R("error", None, "-", "timeout")
    except Exception as e:  # noqa: BLE001
        return _R("error", None, "-", str(e)[:80])


SPECIALS = {
    "deepseek": _deepseek, "openrouter": _openrouter, "stability": _stability,
    "google": _google, "minimax": _minimax, "jina": _jina,
    "cohere": _cohere_check, "deepgram": _deepgram_check, "clipdrop": _clipdrop_check,
}


async def _check_one(pid, session, key, timeout):
    spec = SPECS[pid]
    m = spec.get("method")
    if m == "special":
        return await SPECIALS[pid](session, key, timeout)
    if m == "chat":
        return await _chat(session, key, spec, timeout, pid=pid)
    if m == "embed":
        return await _embed(session, key, spec, timeout)
    if m == "probe":
        return await _probe(session, key, spec, timeout)
    if m == "get":
        return await _get(session, key, spec, timeout)
    return _R("unsupported")


def _detect(key):
    for p, pid in PREFIX_MAP:
        if key.startswith(p):
            return ("single", [pid])
    if key.startswith("sk-"):
        return ("probe", SK_DASH)
    if key.startswith("sk_"):
        return ("probe", SK_UNDER)
    if key.startswith("eyJ"):
        return ("probe", JWT_GROUP)
    if _FALKEY.fullmatch(key):
        return ("single", ["fal"])
    if _UUID.fullmatch(key):
        return ("probe", ["leonardo"])
    if _DOTKEY.fullmatch(key):
        return ("probe", DOT_GROUP)
    if _TOKEN.fullmatch(key):
        return ("loose", [])
    return ("none", [])


class _ProxySession:
    """Thin wrapper around aiohttp.ClientSession that injects a proxy URL
    into every GET/POST call (used for HTTP/HTTPS proxies)."""

    def __init__(self, session: aiohttp.ClientSession, proxy: str):
        self._s = session
        self._p = proxy

    def get(self, url, **kw):
        kw.setdefault("proxy", self._p)
        return self._s.get(url, **kw)

    def post(self, url, **kw):
        kw.setdefault("proxy", self._p)
        return self._s.post(url, **kw)

    def __getattr__(self, name):
        return getattr(self._s, name)


@contextlib.asynccontextmanager
async def _make_session(proxy_url: str):
    """Async context manager that yields a proxy-aware aiohttp session.

    Supported proxy schemes:
      http://  https://          — native aiohttp proxy (injected per-request)
      socks4:// socks4a://       — via aiohttp-socks ProxyConnector
      socks5:// socks5h://       — via aiohttp-socks ProxyConnector
    """
    proxy_url = (proxy_url or "").strip()

    if not proxy_url:
        async with aiohttp.ClientSession() as s:
            yield s
        return

    scheme = proxy_url.split("://")[0].lower() if "://" in proxy_url else ""

    if scheme in ("socks4", "socks4a", "socks5", "socks5h"):
        try:
            from aiohttp_socks import ProxyConnector  # noqa: PLC0415
        except ImportError as exc:
            raise RuntimeError(
                "aiohttp-socks is required for SOCKS proxy. "
                "Run: pip install aiohttp-socks"
            ) from exc
        connector = ProxyConnector.from_url(proxy_url)
        async with aiohttp.ClientSession(connector=connector) as s:
            yield s

    elif scheme in ("http", "https"):
        async with aiohttp.ClientSession() as s:
            yield _ProxySession(s, proxy_url)

    else:
        raise ValueError(
            "Unsupported proxy scheme %r. Use http/https/socks4/socks4a/socks5/socks5h." % scheme
        )


class magent(loader.Module):
    """CLI-агент на базе AI с поддержкой мульти-провайдеров, медиа и автономных системных инструментов."""
    strings = {
        "name": "magent",
        # --- KeyTest (валидатор ключей) ---
        "blk_error": "Ошибки",
        "blk_invalid": "Невалидные",
        "blk_no_balance": "Без баланса",
        "blk_valid": "Рабочие",
        "cat_chat": "Чат / LLM",
        "cat_doc": "OCR / документы",
        "cat_embed": "Эмбеддинги / реранк",
        "cat_image": "Картинки",
        "cat_infra": "Инференс / агрегаторы",
        "cat_music": "Музыка",
        "cat_search": "Поиск / retrieval",
        "cat_tools": "Агентные инструменты",
        "cat_video": "Видео",
        "cat_voice": "Голос / аудио",
        "cfg_deep": "зондировать доп. провайдеров для ключей без префикса (медленнее)",
        "cfg_proxy": "URL прокси (http/https/socks4/socks4a/socks5/socks5h), пусто = без прокси",
        "cfg_show_detail": "показывать строку с деталями",
        "cfg_show_model": "показывать протестированную модель",
        "cfg_timeout": "таймаут запроса, секунды",
        "checkable": "проверяемых",
        "checking": "<i>проверка</i>",
        "checking_n": "<i>проверка {} ключей</i>",
        "file_bad_enc": "Не удалось прочитать файл: не текстовый.",
        "file_reading": "<i>читаю файл…</i>",
        "file_too_big": "Файл слишком большой (макс 2 МБ).",
        "kprov_hint": ".kprov &lt;тип&gt; — полный список одного типа",
        "l_balance": "баланс",
        "l_keys": "ключей",
        "l_model": "модель",
        "l_note": "примечание",
        "l_proxy_ip": "внешний ip",
        "l_proxy_ms": "пинг",
        "l_proxy_url": "прокси",
        "l_status": "статус",
        "m_unknown": "неизвестно",
        "more": "и ещё {}",
        "no_key": "Ответь на сообщение с одним или несколькими API-ключами либо передай ключ аргументом.",
        "providers": "Провайдеры",
        "proxy_err": "ошибка прокси",
        "proxy_ok": "прокси рабочий",
        "proxy_testing": "<i>проверяю прокси…</i>",
        "results_file": "keytest_results.txt",
        "u_chars": "символов",
        "u_credits": "кредитов",
        "u_debt": "долг",
        "u_images": "изображений",
        "u_org": "орг:",
        "u_tokens": "токенов",
        "unknown": "Провайдер не определён или ключ невалиден.",
        "v_error": "ошибка запроса",
        "v_forbidden": "регион заблокирован",
        "v_invalid": "невалидный",
        "v_no_balance": "нет баланса",
        "v_rate_limited": "лимит запросов",
        "v_unsupported": "распознан (без проверки)",
        "v_valid": "рабочий",
        "cfg_api_key_doc": "API ключи Google Gemini, разделенные запятой. Будут скрыты.",
        "cfg_model_name_doc": "Модель AI.",
        "cfg_buttons_doc": "Включить интерактивные кнопки.",
        "cfg_system_instruction_doc": "Системная инструкция (промпт) для AI.",
        "cfg_max_history_length_doc": "Макс. кол-во пар 'вопрос-ответ' в памяти (0 - без лимита).",
        "cfg_timezone_doc": "Ваш часовой пояс. Список: https://en.wikipedia.org/wiki/List_of_tz_database_time_zones",
        "cfg_proxy_doc": "Прокси для обхода региональных блокировок. Формат: http://user:pass@host:port",
        "cfg_impersonation_prompt_doc": "Промпт для режима авто-ответа. {my_name} и {chat_history} будут заменены.",
        "cfg_impersonation_history_limit_doc": "Сколько последних сообщений из чата отправлять в качестве контекста для авто-ответа.",
        "cfg_impersonation_reply_chance_doc": "Вероятность ответа в режиме mauto (от 0.0 до 1.0). 0.2 = 20% шанс.",
        "cfg_temperature_doc": "Температура генерации (креативность). От 0.0 до 2.0. По умолчанию 1.0.",
        "cfg_google_search_doc": "Включить поиск Google (Grounding) для актуальной информации.",
        "cfg_image_model_doc": "Модель Gemini для генерации изображений (например: gemini-2.5-flash-image).",
        "cfg_inline_pagination_doc": "Использовать инлайн-кнопки для длинных ответов.",
        "cfg_global_memory_doc": "Включить ОБЩУЮ память для всех чатов.",
        "cfg_show_tokens_doc": "Показывать токены в ответе, если провайдер их вернул.",
        "cfg_show_time_doc": "Показывать время выполнения запроса.",
        "cfg_auto_model_doc": "Автоматически подбирать модель по профилю и запросу.",
        "cfg_model_profile_doc": "Профиль модели: auto, balanced, fast, reasoning, coding, vision, manual.",
        "cfg_openrouter_model_doc": "Модель OpenRouter (если не задана — используется model_name).",
        "cfg_huggingface_model_doc": "Модель HuggingFace (если не задана — используется model_name).",
        "cfg_openai_model_doc": "Модель OpenAI (если не задана — используется model_name).",
        "cfg_deepseek_model_doc": "Модель DeepSeek (если не задана — используется model_name).",
        "no_api_key": (
            "▲ <b>Api ключ(и) не настроен(ы).</b>\n"
            "⌕ Получить ключи можно:\n"
            "• Google Gemini: <a href=\"https://aistudio.google.com/app/apikey\">здесь</a>\n"
            "• OpenRouter: <a href=\"https://openrouter.ai/settings/keys\">здесь</a>\n"
            "• HuggingFace: <a href=\"https://huggingface.co/settings/tokens\">здесь</a>\n"
            "• OpenAI: <a href=\"https://platform.openai.com/api-keys\">здесь</a>\n"
            "• DeepSeek: <a href=\"https://platform.deepseek.com/api_keys\">здесь</a>\n"
            "<b>Добавьте ключ(и) в конфиге модуля:</b> <code>.cfg magent api_key</code>"
        ),
        "no_api_key_openrouter": "▲ <b>API ключ для OpenRouter не настроен.</b>\nПолучить ключ можно <a href=\"https://openrouter.ai/settings/keys\">здесь</a>.\n<b>Добавьте ключ в конфиге модуля:</b> <code>.cfg magent openrouter_api_key</code>",
        "no_api_key_huggingface": "▲ <b>API ключ для HuggingFace не настроен.</b>\nПолучить ключ можно <a href=\"https://huggingface.co/settings/tokens\">здесь</a>.\n<b>Добавьте ключ в конфиге модуля:</b> <code>.cfg magent huggingface_api_key</code>",
        "no_api_key_openai": "▲ <b>API ключ для OpenAI не настроен.</b>\nПолучить ключ можно <a href=\"https://platform.openai.com/api-keys\">здесь</a>.\n<b>Добавьте ключ в конфиге модуля:</b> <code>.cfg magent openai_api_key</code>",
        "no_api_key_deepseek": "▲ <b>API ключ для DeepSeek не настроен.</b>\nПолучить ключ можно <a href=\"https://platform.deepseek.com/api_keys\">здесь</a>.\n<b>Добавьте ключ в конфиге модуля:</b> <code>.cfg magent deepseek_api_key</code>",
        "invalid_api_key_openrouter": "▲ <b>Предоставленный API ключ OpenRouter недействителен.</b>",
        "invalid_api_key_huggingface": "▲ <b>Предоставленный API ключ HuggingFace недействителен.</b>",
        "invalid_api_key_openai": "▲ <b>Предоставленный API ключ OpenAI недействителен.</b>",
        "invalid_api_key_deepseek": "▲ <b>Предоставленный API ключ DeepSeek недействителен.</b>",
        "gmodel_list_title_openrouter": "∅ <b>Доступные модели OpenRouter:</b>",
        "gmodel_list_title_huggingface": "∅ <b>Доступные модели HuggingFace:</b>",
        "gmodel_list_title_openai": "∅ <b>Доступные модели OpenAI:</b>",
        "gmodel_list_title_deepseek": "∅ <b>Доступные модели DeepSeek:</b>",
        "invalid_api_key": "▲ <b>Предоставленный API ключ Google недействителен.</b>",
        "all_keys_exhausted": "▲ <b>Все доступные API ключи ({}) исчерпали свою квоту.</b>\nПопробуйте позже или добавьте новые ключи в конфиге: <code>.cfg magent api_key</code>",
        "no_prompt_or_media": "▲ <i>Нужен текст или ответ на медиа/файл.</i>",
        "processing": "🌸 <b>Обработка...</b>",
        "api_error": "▲ <b>Ошибка API:</b>\n<code>{}</code>",
        "api_timeout": f"▲ <b>Таймаут ответа от API ({GEMINI_TIMEOUT} сек).</b>",
        "blocked_error": "▲ <b>Запрос/ответ заблокирован.</b>\n<code>{}</code>",
        "generic_error": "▲ <b>Ошибка:</b>\n<code>{}</code>",
        "question_prefix": "» <b>Запрос:</b>",
        "response_prefix": "✦ <b>AI:</b>",
        "unsupported_media_type": "▲ <b>Формат медиа ({}) не поддерживается.</b>",
        "memory_status": "⏣ [{}/{}]",
        "memory_status_unlimited": "⏣ [{}/∞]",
        "memory_status_global": "⏣ [◎ GLOBAL/{}]",
        "memory_cleared": "⌫ <b>Память диалога очищена.</b>",
        "memory_cleared_global": "⌫ <b>Глобальная память очищена.</b>",
        "memory_cleared_gauto": "⌫ <b>Память mauto в этом чате очищена.</b>",
        "no_memory_to_clear": "⌕ <b>В этом чате нет истории.</b>",
        "gres_global_cleared": "⌫ <b>Вся глобальная память очищена.</b>",
        "gres_no_global": "⌕ <b>Глобальная память и так пуста.</b>",
        "no_gauto_memory_to_clear": "⌕ <b>В этом чате нет истории mauto.</b>",
        "memory_chats_title": "⏣ <b>Чаты с историей ({}):</b>",
        "memory_chat_line": "  • {} (<code>{}</code>)",
        "no_memory_found": "⌕ Память AI пуста.",
        "media_reply_placeholder": "[ответ на медиа]",
        "btn_clear": "⌫ Очистить",
        "btn_regenerate": "↺ Другой ответ",
        "no_last_request": "Последний запрос не найден для повторной генерации.",
        "memory_fully_cleared": "⌫ <b>Вся память полностью очищена (затронуто {} чатов).</b>",
        "gauto_memory_fully_cleared": "⌫ <b>Вся память mauto полностью очищена (затронуто {} чатов).</b>",
        "no_memory_to_fully_clear": "⌕ <b>Память и так пуста.</b>",
        "no_gauto_memory_to_fully_clear": "⌕ <b>Память mauto и так пуста.</b>",
        "response_too_long": "Ответ AI был слишком длинным и отправлен в виде файла.",
        "gclear_usage": "⌕ <b>Использование:</b> <code>.mclear [global/auto]</code>",
        "gres_usage": "⌕ <b>Использование:</b> <code>.mres [global/auto]</code>",
        "auto_mode_on": "⍟ <b>Режим авто-ответа включен в этом чате.</b>\nЯ буду отвечать на сообщения с вероятностью {}%.",
        "auto_mode_off": "⍟ <b>Режим авто-ответа выключен в этом чате.</b>",
        "auto_mode_chats_title": "⍟ <b>Чаты с активным авто-ответом ({}):</b>",
        "no_auto_mode_chats": "⌕ Нет чатов с включенным режимом авто-ответа.",
        "auto_mode_usage": "⌕ <b>Использование:</b> <code>.mauto on/off или [id/username] [on/off]</code>",
        "gauto_chat_not_found": "▲ <b>Не удалось найти чат:</b> <code>{}</code>",
        "gauto_state_updated": "⍟ <b>Режим авто-ответа для чата {} {}</b>",
        "gauto_enabled": "включен",
        "gauto_disabled": "выключен",
        "gch_usage": "⌕ <b>Использование:</b>\n<code>.mch <кол-во> <вопрос></code>\n<code>.mch <id чата> <кол-во> <вопрос></code>",
        "gch_processing": "🌸 <b>Анализирую {} сообщений...</b>",
        "gch_result_caption": "Анализ последних {} сообщений",
        "gch_result_caption_from_chat": "Анализ последних {} сообщений из чата <b>{}</b>",
        "gch_invalid_args": "▲ <b>Неверные аргументы.</b>\n{}",
        "gch_chat_error": "▲ <b>Ошибка доступа к чату</b> <code>{}</code>: <i>{}</i>",
        "gask_no_prompt": "▲ <b>Введите вопрос или ответьте командой на сообщение.</b>",
        "gprovider_usage": "⌕ <b>Использование:</b> <code>.mprovider [gemini/openrouter/huggingface/openai/deepseek/groq/mistral/together/cerebras/xai/nvidia/custom]</code>",
        "gprovider_current": (
            "⌘ <b>Текущий провайдер:</b> <code>{}</code>\n"
            "⌬ <b>Модель:</b> <code>{}</code>\n\n"
            "<b>Все модели:</b>\n"
            "✦ Gemini: <code>{}</code>\n"
            "✦ OpenRouter: <code>{}</code>\n"
            "✦ HuggingFace: <code>{}</code>\n"
            "✦ OpenAI: <code>{}</code>\n"
            "✦ DeepSeek: <code>{}</code>\n\n"
            "<code>.mmodel</code> — сменить модель\n"
            "<code>.mprovider</code> — сменить провайдера"
        ),
        "gprovider_set": "✓ <b>Провайдер:</b> <code>{}</code>\n⌬ <b>Модель:</b> <code>{}</code>",
        "gprofile_usage": "⌕ <b>Использование:</b> <code>.mprofile [auto|balanced|fast|reasoning|coding|vision|manual]</code>",
        "gprofile_set": "✓ <b>Профиль модели:</b> <code>{}</code>\n⌬ <b>Для текущего провайдера:</b> <code>{}</code>",
        "gmodel_usage": "⌕ <b>Использование:</b> <code>.mmodel [модель] [--s|-s]</code>\n• [модель] — установить модель.\n• --s/-s — показать список доступных моделей (или <code>.mmodels</code>).",
        "gmodels_usage": "⌕ <b>Использование:</b> <code>.mmodels [провайдер] [поиск]</code>\n• Интерактивное инлайн-меню моделей провайдера из API (curl) с выбором по кнопке.",
        "gmodel_list_title": "∅ <b>Доступные модели Gemini (по вашему API):</b>",
        "gmodel_list_item": "• <code>{}</code> — {} (поддержка: {})",
        "gmodel_img_support": "Поддержка изображений",
        "gmodel_no_support": "Нет поддержки изображений",
        "gmodel_img_warn": "▲ <b>Текущая модель ({}) не может генерировать изображения(или не доступна по API).</b>\nРекомендуем: <code>gemini-2.5-flash-image</code>",
        "gme_chat_not_found": "▲ <b>Не удалось найти чат для экспорта:</b> <code>{}</code>",
        "gme_sent_to_saved": "⎙ История экспортирована в избранное.",
        "new_sdk_missing": "▲ <b>Для работы модуля нужна библиотека google-genai.</b>\nВыполните: <code>pip install google-genai</code>",
        "gprompt_usage": "⌕ <b>Использование:</b>\n<code>.mprompt <текст/пресет></code> — установить.\n<code>.mprompt -c</code> — очистить.\n<code>.mpresets</code> — база пресетов.",
        "gprompt_updated": "✓ <b>Системный промпт обновлен!</b>\nДлина: {} символов.",
        "gprompt_cleared": "⌫ <b>Системный промпт очищен.</b>",
        "gprompt_current": "» <b>Текущий системный промпт:</b>",
        "gprompt_file_error": "▲ <b>Ошибка чтения файла:</b> {}",
        "gprompt_file_too_big": "▲ <b>Файл слишком большой</b> (лимит 1 МБ).",
        "gprompt_not_text": "▲ Это не похоже на текстовый файл.(txt)",
        "gmodel_no_models": "▲ Не удалось получить список моделей.",
        "gmodel_list_error": "▲ Ошибка получения списка: {}",
        "gimg_process": "✦ <b>Генерация...</b>\n⌬ <i>Модель: {model}</i>",
        "gpresets_usage": (
            "⌕ <b>Управление пресетами:</b>\n"
            "• <code>.mpresets save [Имя] текст</code> — сохранить (имя в скобках, если с пробелами).\n"
            "• <code>.mpresets load 1</code> или <code>имя</code> — загрузить по номеру/имени.\n"
            "• <code>.mpresets del 1</code> или <code>имя</code> — удалить.\n"
            "• <code>.mpresets list</code> — список."
        ),
        "gpreset_loaded": "✓ <b>Установлен пресет:</b> [<code>{}</code>]\nДлина: {} симв.", 
        "gpreset_saved": "⎙ <b>Пресет сохранен!</b>\n∅ <b>Имя:</b> {}\n№ <b>Индекс:</b> {}",
        "gpreset_deleted": "⌫ <b>Пресет удален:</b> {}",
        "gpreset_not_found": "▲ Пресет с таким именем или индексом не найден.",
        "gpreset_list_head": "∅ <b>Ваши пресеты:</b>\n",
        "gpreset_empty": "⌕ Список пресетов пуст.",
        "tools_status": (
            "⎈ <b>Инструменты-агент:</b> {}\n"
            "⬡ <b>Доступно:</b> <code>run_terminal</code>, <code>read_file</code>, <code>write_file</code>, <code>list_dir</code>, <code>tg_send</code>, <code>tg_history</code>, <code>web_search</code>, <code>fetch_url</code>\n"
            "◈ <b>Шаги/таймаут:</b> {} / {}с · <b>Провайдер:</b> <code>{}</code>\n\n"
            "▲ <i>Доступ к шеллу хоста. Только при ваших вызовах <code>.m</code>/<code>.mt</code>; в mauto отключено. Работают у всех провайдеров с поддержкой tool-calling (Gemini, OpenAI, OpenRouter, Groq, Mistral, DeepSeek, xAI, Together и т.д.).</i>\n"
            "<code>.mtools on/off</code> — переключить."
        ),
        "tools_on": "✓ <b>Инструменты включены.</b>",
        "tools_off": "✗ <b>Инструменты выключены.</b>",
        "tools_need_gemini": "▲ <b>Инструменты работают только с провайдером <code>gemini</code>.</b> Сейчас: <code>{}</code>.\nПереключи: <code>.mprovider gemini</code>",
        "tools_running": "⎈ <i>{}</i>",
        "tools_progress_head": (
            "◴ <b>Обработка...</b> <i>· шаг {}</i>\n"
            "⎈ <b>Выполнение команд:</b>"
        ),
        "gstat": (
            "∷ <b>Статистика magent-агента</b>\n"
            "◴ <b>Аптайм сессии:</b> {uptime}\n\n"
            "⌘ <b>Провайдер:</b> <code>{provider}</code> · профиль <code>{profile}</code>\n"
            "⌬ <b>Модель:</b> <code>{model}</code>\n"
            "⚿ <b>Ключи Gemini:</b> {g_keys} (в кулдауне: {cooldowns})\n"
            "⬡ <b>Настроены:</b> {configured}\n\n"
            "∷ <b>Запросов:</b> {requests} · <b>ср/посл:</b> {avg_t}с / {last_t}с\n"
            "◈ <b>Токены:</b> {t_total} (in {t_in} / out {t_out})\n\n"
            "⏣ <b>Память:</b> {chats} чат(ов), {pairs} пар · режим {mem_mode}\n"
            "⍟ <b>Mauto:</b> {gauto_chats} истор. · активно {imp_chats} · память off в {mem_off}\n"
            "∅ <b>Пресетов:</b> {presets}\n"
            "⎈ <b>Инструменты-агент:</b> {tools_state}"
        ),
    }
    TEXT_MIME_TYPES = {
        "text/plain", "text/markdown", "text/html", "text/css", "text/csv",
        "application/json", "application/xml", "application/x-python", "text/x-python",
        "application/javascript", "application/x-sh",
    }

    CORE_PROVIDER_ORDER = ("google", "openrouter", "huggingface", "openai", "deepseek", "groq", "mistral", "together", "cerebras", "xai", "nvidia", "custom")

    PROVIDER_SPECS = {
        "google": {
            "label": "Gemini",
            "default_model": "gemini-3-flash-preview",
            "docs_url": "https://ai.google.dev/gemini-api/docs/models",
            "model_prefixes": ("gemini", "imagen", "lyria", "veo"),
            "profiles": {
                "balanced": "gemini-3-flash-preview",
                "fast": "gemini-2.5-flash",
                "reasoning": "gemini-3.1-pro-preview",
                "coding": "gemini-3.1-pro-preview-custom-tools",
                "vision": "gemini-3-flash-preview",
            },
            "fallback_models": (
                "gemini-3-flash-preview",
                "gemini-2.5-flash",
                "gemini-2.5-pro",
                "gemini-2.5-flash-lite",
                "gemini-2.5-flash-image",
            ),
        },
        "openrouter": {
            "label": "OpenRouter",
            "default_model": "google/gemini-3-flash-preview",
            "docs_url": "https://openrouter.ai/docs/docs/overview/models",
            "model_prefixes": ("/",),
            "profiles": {
                "balanced": "google/gemini-3-flash-preview",
                "fast": "google/gemini-3.1-flash-lite-preview",
                "reasoning": "google/gemini-3.1-pro-preview",
                "coding": "anthropic/claude-sonnet-4.6",
                "vision": "google/gemini-3-flash-preview",
            },
            "fallback_models": (
                "google/gemini-3-flash-preview",
                "google/gemini-2.5-flash",
                "google/gemini-2.5-pro",
                "anthropic/claude-sonnet-4",
                "openai/gpt-4o",
                "deepseek/deepseek-r1",
            ),
        },
        "huggingface": {
            "label": "HuggingFace",
            "default_model": "Qwen/Qwen2.5-Coder-32B-Instruct",
            "docs_url": "https://huggingface.co/docs/api-inference",
            "model_prefixes": ("/", "meta-", "mistral", "google", "Qwen", "deepseek", "microsoft"),
            "profiles": {
                "balanced": "Qwen/Qwen2.5-Coder-32B-Instruct",
                "fast": "Qwen/Qwen3-4B",
                "reasoning": "deepseek-ai/DeepSeek-R1",
                "coding": "Qwen/Qwen2.5-Coder-32B-Instruct",
                "vision": "Qwen/Qwen2.5-VL-72B-Instruct",
            },
            "fallback_models": (
                "Qwen/Qwen2.5-Coder-32B-Instruct",
                "Qwen/Qwen3-4B",
                "deepseek-ai/DeepSeek-R1",
                "Qwen/Qwen2.5-VL-72B-Instruct",
                "Qwen/Qwen3-30B-A3B",
                "microsoft/Phi-4-mini-instruct",
                "HuggingFaceTB/SmolLM2-1.7B-Instruct",
            ),
        },
        "openai": {
            "label": "OpenAI",
            "default_model": "gpt-4o",
            "docs_url": "https://platform.openai.com/docs/models",
            "model_prefixes": ("gpt-", "o1-", "o3-", "chatgpt-"),
            "profiles": {
                "balanced": "gpt-4o",
                "fast": "gpt-4o-mini",
                "reasoning": "o1-preview",
                "coding": "gpt-4o",
                "vision": "gpt-4o",
            },
            "fallback_models": (
                "gpt-4o",
                "gpt-4o-mini",
                "gpt-4-turbo",
                "o1-preview",
                "o1-mini",
                "chatgpt-4o-latest",
            ),
        },
        "deepseek": {
            "label": "DeepSeek",
            "default_model": "deepseek-chat",
            "docs_url": "https://platform.deepseek.com/docs",
            "model_prefixes": ("deepseek-",),
            "profiles": {
                "balanced": "deepseek-chat",
                "fast": "deepseek-chat",
                "reasoning": "deepseek-reasoner",
                "coding": "deepseek-coder",
                "vision": "deepseek-chat",
            },
            "fallback_models": (
                "deepseek-chat",
                "deepseek-reasoner",
                "deepseek-coder",
            ),
        },
        "groq": {
            "label": "Groq",
            "default_model": "llama-3.3-70b-versatile",
            "docs_url": "https://console.groq.com/docs/models",
            "model_prefixes": ("llama", "mixtral", "gemma", "qwen", "deepseek", "moonshotai", "/"),
            "profiles": {
                "balanced": "llama-3.3-70b-versatile",
                "fast": "llama-3.1-8b-instant",
                "reasoning": "deepseek-r1-distill-llama-70b",
                "coding": "qwen-2.5-coder-32b",
                "vision": "llama-3.2-90b-vision-preview",
            },
            "fallback_models": (
                "llama-3.3-70b-versatile",
                "llama-3.1-8b-instant",
                "deepseek-r1-distill-llama-70b",
                "mixtral-8x7b-32768",
                "gemma2-9b-it",
            ),
        },
        "mistral": {
            "label": "Mistral",
            "default_model": "mistral-large-latest",
            "docs_url": "https://docs.mistral.ai/getting-started/models/",
            "model_prefixes": ("mistral", "open-", "codestral", "pixtral", "ministral", "magistral", "/"),
            "profiles": {
                "balanced": "mistral-large-latest",
                "fast": "mistral-small-latest",
                "reasoning": "magistral-medium-latest",
                "coding": "codestral-latest",
                "vision": "pixtral-large-latest",
            },
            "fallback_models": (
                "mistral-large-latest",
                "mistral-small-latest",
                "codestral-latest",
                "pixtral-large-latest",
                "open-mistral-nemo",
            ),
        },
        "together": {
            "label": "Together",
            "default_model": "meta-llama/Llama-3.3-70B-Instruct-Turbo",
            "docs_url": "https://docs.together.ai/docs/inference-models",
            "model_prefixes": ("/", "meta-", "Qwen", "deepseek", "mistralai", "google", "NousResearch"),
            "profiles": {
                "balanced": "meta-llama/Llama-3.3-70B-Instruct-Turbo",
                "fast": "meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo",
                "reasoning": "deepseek-ai/DeepSeek-R1",
                "coding": "Qwen/Qwen2.5-Coder-32B-Instruct",
                "vision": "meta-llama/Llama-3.2-90B-Vision-Instruct-Turbo",
            },
            "fallback_models": (
                "meta-llama/Llama-3.3-70B-Instruct-Turbo",
                "deepseek-ai/DeepSeek-R1",
                "Qwen/Qwen2.5-Coder-32B-Instruct",
                "mistralai/Mixtral-8x7B-Instruct-v0.1",
            ),
        },
        "cerebras": {
            "label": "Cerebras",
            "default_model": "llama-3.3-70b",
            "docs_url": "https://inference-docs.cerebras.ai/models",
            "model_prefixes": ("llama", "qwen", "deepseek", "/"),
            "profiles": {
                "balanced": "llama-3.3-70b",
                "fast": "llama3.1-8b",
                "reasoning": "deepseek-r1-distill-llama-70b",
                "coding": "qwen-3-coder-480b",
                "vision": "llama-3.3-70b",
            },
            "fallback_models": (
                "llama-3.3-70b",
                "llama3.1-8b",
                "qwen-3-235b-a22b-instruct",
                "deepseek-r1-distill-llama-70b",
            ),
        },
        "xai": {
            "label": "xAI Grok",
            "default_model": "grok-4",
            "docs_url": "https://docs.x.ai/docs/models",
            "model_prefixes": ("grok", "/"),
            "profiles": {
                "balanced": "grok-4",
                "fast": "grok-3-mini",
                "reasoning": "grok-4",
                "coding": "grok-code-fast-1",
                "vision": "grok-4",
            },
            "fallback_models": (
                "grok-4",
                "grok-3",
                "grok-3-mini",
                "grok-code-fast-1",
            ),
        },
        "nvidia": {
            "label": "Nvidia NIM",
            "default_model": "meta/llama-3.3-70b-instruct",
            "docs_url": "https://build.nvidia.com/models",
            "model_prefixes": ("/", "meta/", "qwen/", "deepseek-ai/", "mistralai/", "nvidia/", "google/"),
            "profiles": {
                "balanced": "meta/llama-3.3-70b-instruct",
                "fast": "meta/llama-3.1-8b-instruct",
                "reasoning": "deepseek-ai/deepseek-r1",
                "coding": "qwen/qwen2.5-coder-32b-instruct",
                "vision": "meta/llama-3.2-90b-vision-instruct",
            },
            "fallback_models": (
                "meta/llama-3.3-70b-instruct",
                "deepseek-ai/deepseek-r1",
                "qwen/qwen2.5-coder-32b-instruct",
                "nvidia/llama-3.1-nemotron-70b-instruct",
            ),
        },
        "custom": {
            "label": "Custom",
            "default_model": "gpt-4o",
            "docs_url": "",
            "model_prefixes": ("",),
            "profiles": {},
            "fallback_models": (),
        },
    }

    # OpenAI-совместимые эндпоинты (chat/completions). custom берётся из конфига.
    OPENAI_COMPAT_ENDPOINTS = {
        "openrouter": "https://openrouter.ai/api/v1/chat/completions",
        "openai": "https://api.openai.com/v1/chat/completions",
        "deepseek": "https://api.deepseek.com/v1/chat/completions",
        "groq": "https://api.groq.com/openai/v1/chat/completions",
        "mistral": "https://api.mistral.ai/v1/chat/completions",
        "together": "https://api.together.xyz/v1/chat/completions",
        "cerebras": "https://api.cerebras.ai/v1/chat/completions",
        "xai": "https://api.x.ai/v1/chat/completions",
        "nvidia": "https://integrate.api.nvidia.com/v1/chat/completions",
    }

    # provider -> имя конфига с моделью этого провайдера
    PROVIDER_MODEL_CFG = {
        "openrouter": "openrouter_model", "huggingface": "huggingface_model",
        "openai": "openai_model", "deepseek": "deepseek_model", "groq": "groq_model",
        "mistral": "mistral_model", "together": "together_model", "cerebras": "cerebras_model",
        "xai": "xai_model", "nvidia": "nvidia_model", "custom": "custom_model",
    }

    # provider -> имя конфига с API-ключом этого провайдера
    PROVIDER_KEY_CFG = {
        "google": "api_key",
        "openrouter": "openrouter_api_key",
        "huggingface": "huggingface_api_key",
        "openai": "openai_api_key",
        "deepseek": "deepseek_api_key",
        "groq": "groq_api_key",
        "mistral": "mistral_api_key",
        "together": "together_api_key",
        "cerebras": "cerebras_api_key",
        "xai": "xai_api_key",
        "nvidia": "nvidia_api_key",
        "custom": "custom_api_key",
    }

    def __init__(self):
        self.config = loader.ModuleConfig(
            loader.ConfigValue("api_key", "", self.strings["cfg_api_key_doc"], validator=loader.validators.Hidden()),
            loader.ConfigValue("openrouter_api_key", "", "API Key от OpenRouter (получить <a href='https://openrouter.ai/settings/keys'>тут</a>).", validator=loader.validators.Hidden()),
            loader.ConfigValue("huggingface_api_key", "", "API Key от HuggingFace (получить <a href='https://huggingface.co/settings/tokens'>тут</a>).", validator=loader.validators.Hidden()),
            loader.ConfigValue("openai_api_key", "", "API Key от OpenAI (получить <a href='https://platform.openai.com/api-keys'>тут</a>).", validator=loader.validators.Hidden()),
            loader.ConfigValue("deepseek_api_key", "", "API Key от DeepSeek (получить <a href='https://platform.deepseek.com/api_keys'>тут</a>).", validator=loader.validators.Hidden()),
            loader.ConfigValue("provider", "google", "Провайдер API.", validator=loader.validators.Choice(["google", "openrouter", "huggingface", "openai", "deepseek", "groq", "mistral", "together", "cerebras", "xai", "nvidia", "custom"])),
            loader.ConfigValue("model_name", "gemini-3-flash-preview", self.strings["cfg_model_name_doc"]),
            loader.ConfigValue("openrouter_model", "", self.strings["cfg_openrouter_model_doc"]),
            loader.ConfigValue("huggingface_model", "", self.strings["cfg_huggingface_model_doc"]),
            loader.ConfigValue("openai_model", "", self.strings["cfg_openai_model_doc"]),
            loader.ConfigValue("deepseek_model", "", self.strings["cfg_deepseek_model_doc"]),
            loader.ConfigValue("groq_api_key", "", "API Key от Groq (console.groq.com/keys).", validator=loader.validators.Hidden()),
            loader.ConfigValue("groq_model", "", "Модель Groq (если пусто — из спеки/model_name)."),
            loader.ConfigValue("mistral_api_key", "", "API Key от Mistral (console.mistral.ai).", validator=loader.validators.Hidden()),
            loader.ConfigValue("mistral_model", "", "Модель Mistral (если пусто — из спеки/model_name)."),
            loader.ConfigValue("together_api_key", "", "API Key от Together AI (api.together.xyz).", validator=loader.validators.Hidden()),
            loader.ConfigValue("together_model", "", "Модель Together (если пусто — из спеки/model_name)."),
            loader.ConfigValue("cerebras_api_key", "", "API Key от Cerebras (cloud.cerebras.ai).", validator=loader.validators.Hidden()),
            loader.ConfigValue("cerebras_model", "", "Модель Cerebras (если пусто — из спеки/model_name)."),
            loader.ConfigValue("xai_api_key", "", "API Key от xAI Grok (console.x.ai).", validator=loader.validators.Hidden()),
            loader.ConfigValue("xai_model", "", "Модель xAI Grok (если пусто — из спеки/model_name)."),
            loader.ConfigValue("nvidia_api_key", "", "API Key от Nvidia NIM (build.nvidia.com).", validator=loader.validators.Hidden()),
            loader.ConfigValue("nvidia_model", "", "Модель Nvidia NIM (если пусто — из спеки/model_name)."),
            loader.ConfigValue("custom_api_key", "", "API Key для кастомного OpenAI-совместимого провайдера.", validator=loader.validators.Hidden()),
            loader.ConfigValue("custom_base_url", "", "Базовый URL кастомного провайдера. Можно полный (.../chat/completions) или корень (.../v1)."),
            loader.ConfigValue("custom_model", "", "Модель кастомного провайдера."),
            loader.ConfigValue("custom_label", "Custom", "Отображаемое имя кастомного провайдера."),
            loader.ConfigValue("interactive_buttons", True, self.strings["cfg_buttons_doc"], validator=loader.validators.Boolean()),
            loader.ConfigValue("system_instruction", "", self.strings["cfg_system_instruction_doc"], validator=loader.validators.String()),
            loader.ConfigValue("max_history_length", 800, self.strings["cfg_max_history_length_doc"], validator=loader.validators.Integer(minimum=0)),
            loader.ConfigValue("global_memory", False, self.strings["cfg_global_memory_doc"], validator=loader.validators.Boolean()),
            loader.ConfigValue("show_tokens", True, self.strings["cfg_show_tokens_doc"], validator=loader.validators.Boolean()),
            loader.ConfigValue("show_time", True, self.strings["cfg_show_time_doc"], validator=loader.validators.Boolean()),
            loader.ConfigValue("auto_model", False, self.strings["cfg_auto_model_doc"], validator=loader.validators.Boolean()),
            loader.ConfigValue("model_profile", "manual", self.strings["cfg_model_profile_doc"], validator=loader.validators.Choice(list(MODEL_PROFILE_CHOICES))),
            loader.ConfigValue("timezone", "Europe/Moscow", self.strings["cfg_timezone_doc"]),
            loader.ConfigValue("proxy", "", self.strings["cfg_proxy_doc"]),
            loader.ConfigValue(
                "impersonation_prompt",
                (
                    "Ты — это я, пользователь Telegram по имени {my_name}. Твоя задача — отвечать в чате от моего имени, основываясь на последних сообщениях. "
                    "Веди себя естественно, как обычный человек, а не как ассистент. Не признавайся, что ты — ИИ, даже если тебя спросят напрямую. "
                    "Твоя личность:[Здесь опишите свой характер: остроумный, серьезный, саркастичный, дружелюбный и т.д.].\n"
                    "Правила:\n- Отвечай кратко и по делу.\n- Используй неформальный язык, сленг.\n- Не отвечай на каждое сообщение.\n- На медиа (стикер, фото) реагируй как человек ('лол', 'ору', 'жиза').\n- Не используй префиксы и кавычки.\n\n"
                    "ИСТОРИЯ ЧАТА:\n{chat_history}\n\n{my_name}:"
                ),
                self.strings["cfg_impersonation_prompt_doc"], validator=loader.validators.String()
            ),
            loader.ConfigValue("impersonation_history_limit", 20, self.strings["cfg_impersonation_history_limit_doc"], validator=loader.validators.Integer(minimum=5, maximum=100)),
            loader.ConfigValue("impersonation_reply_chance", 0.25, self.strings["cfg_impersonation_reply_chance_doc"], validator=loader.validators.Float(minimum=0.0, maximum=1.0)),
            loader.ConfigValue("gauto_in_pm", False, "Разрешить авто-ответы в личных сообщениях (ЛС).", validator=loader.validators.Boolean()),
            loader.ConfigValue("google_search", False, self.strings["cfg_google_search_doc"], validator=loader.validators.Boolean()),
            loader.ConfigValue("temperature", 1.0, self.strings["cfg_temperature_doc"], validator=loader.validators.Float(minimum=0.0, maximum=2.0)),
            loader.ConfigValue("inline_pagination", False, self.strings["cfg_inline_pagination_doc"], validator=loader.validators.Boolean()),
            loader.ConfigValue("image_model_name", "gemini-2.5-flash-image", self.strings["cfg_image_model_doc"]),
            loader.ConfigValue(
                "enable_tools", False,
                "⎈ Инструменты-агент (function-calling у всех провайдеров с поддержкой tools): терминал, файлы/код, Telegram. "
                "ВНИМАНИЕ: даёт AI доступ к шеллу хоста. Работает только при ВАШИХ вызовах .m/.mt, в mauto отключено.",
                validator=loader.validators.Boolean()
            ),
            loader.ConfigValue("tools_shell_timeout", 60, "Таймаут команды терминала (сек).", validator=loader.validators.Integer(minimum=1, maximum=3600)),
            loader.ConfigValue("tools_workdir", "", "Рабочая директория для инструментов (пусто = текущая)."),
            loader.ConfigValue("tools_max_iters", 1000000, "Макс. кол-во шагов вызова инструментов за один запрос.", validator=loader.validators.Integer(minimum=1, maximum=2000000)),
            loader.ConfigValue("tools_output_limit", 6000, "Лимит символов вывода одного инструмента.", validator=loader.validators.Integer(minimum=500, maximum=30000)),
            loader.ConfigValue("tools_confirm", False, "Спрашивать подтверждение перед каждой командой терминала (выводит в лог).", validator=loader.validators.Boolean()),
            loader.ConfigValue("premium_emoji_refresh", True, "Доп. перерисовка финального ответа, чтобы подхватились премиум-эмодзи (нужен Telegram Premium у аккаунта).", validator=loader.validators.Boolean()),
            loader.ConfigValue("rich_mode", True, "Включить Telegram Rich Mode (нативные детали <details>, thinking-блоки модели, таблицы и расширенная разметка).", validator=loader.validators.Boolean()),
            loader.ConfigValue("clean_symbols_mode", True, "Режим без эмодзи: заменять все эмодзи (в т.ч. премиум) на строгие текстовые Unicode-символы.", validator=loader.validators.Boolean()),
            loader.ConfigValue("show_tool_calls_in_response", True, "Показывать результаты инструментов и ход работы в итоговом ответе AI.", validator=loader.validators.Boolean()),
            # --- KeyTest (валидатор ключей: .keytest / .kprov / .kproxytest) ---
            loader.ConfigValue("kt_timeout", 20, "KeyTest: таймаут запроса проверки ключа, сек.", validator=loader.validators.Integer(minimum=5, maximum=120)),
            loader.ConfigValue("kt_show_model", True, "KeyTest: показывать протестированную модель.", validator=loader.validators.Boolean()),
            loader.ConfigValue("kt_show_detail", False, "KeyTest: показывать доп. строку с деталями.", validator=loader.validators.Boolean()),
            loader.ConfigValue("kt_deep", False, "KeyTest: зондировать доп. провайдеров для ключей без префикса (медленнее).", validator=loader.validators.Boolean()),
            loader.ConfigValue("kt_proxy", "", "KeyTest: URL прокси (http/https/socks4/socks4a/socks5/socks5h), пусто = без прокси.", validator=loader.validators.Hidden(loader.validators.String())),
        )
        self.prompt_presets = []
        self._tool_steps = []
        self._tool_start_time = 0.0
        self.conversations = {}
        self.gauto_conversations = {}
        self.last_requests = {}
        self.impersonation_chats = set()
        self._lock = asyncio.Lock()
        self.memory_disabled_chats = set()
        self.pager_cache = {}
        self.key_model_map = {}
        self.provider_models = {}
        self.key_cooldowns = {}
        self.models_menu_cache = {}
        self._provider_models_api_cache = {}
        self._kt_keys_cache = {}
        self._pending_keys = {}
        self._current_tool_chat_id = None
        self._current_tool_message = None
        self.session_stats = {"requests": 0, "tokens_in": 0, "tokens_out": 0, "times": [], "start_time": time.time(), "by_provider": {}}
        self.api_keys = [] 

    async def client_ready(self, client, db):
        self.client = client
        self.db = db
        self.me = await client.get_me()
        self.models_menu_cache = {}
        self._provider_models_api_cache = {}
        self._pending_keys = {}
        self._kt_keys_cache = {}
        api_key_str = self.config["api_key"]
        self.api_keys = [k.strip() for k in api_key_str.split(",") if k.strip()] if api_key_str else []
        def _get_db(k, default=None):
            val = self.db.get(self.strings["name"], k, None)
            if (val is None or not val) and self.strings["name"] != "Gemini":
                legacy = self.db.get("Gemini", k, None)
                if legacy is not None:
                    return legacy
            return default if val is None else val

        self.key_model_map = _get_db(DB_KEY_MAP_KEY, {})
        self.provider_models = _get_db(DB_PROVIDER_MODELS_KEY, {})
        if not isinstance(self.provider_models, dict):
            self.provider_models = {}
        self.memory_disabled_chats = set(_get_db(DB_MEMORY_DISABLED_KEY, []))
        saved_stats = _get_db(DB_SESSION_STATS_KEY, {})
        if isinstance(saved_stats, dict):
            self.session_stats.update({
                "requests": int(saved_stats.get("requests", 0) or 0),
                "tokens_in": int(saved_stats.get("tokens_in", 0) or 0),
                "tokens_out": int(saved_stats.get("tokens_out", 0) or 0),
                "times": list(saved_stats.get("times", []) or [])[-200:],
                "start_time": time.time(),
                "by_provider": dict(saved_stats.get("by_provider", {}) or {}),
            })
        keys_to_remove = [k for k in self.key_model_map if k not in self.api_keys]
        if keys_to_remove:
            for k in keys_to_remove: del self.key_model_map[k]
            self.db.set(self.strings["name"], DB_KEY_MAP_KEY, self.key_model_map)
        if not GOOGLE_AVAILABLE:
            logger.error("magent: 'google-genai' library missing! pip install google-genai")
            return
        self.current_api_key_index = 0
        self.conversations = self._load_history_from_db(DB_HISTORY_KEY)
        self.prompt_presets = _get_db(DB_PRESETS_KEY, [])
        if isinstance(self.prompt_presets, dict):
            self.prompt_presets = [{"name": k, "content": v} for k, v in self.prompt_presets.items()]
        self.gauto_conversations = self._load_history_from_db(DB_GAUTO_HISTORY_KEY)
        self.impersonation_chats = set(_get_db(DB_IMPERSONATION_KEY, []))
        self.pager_cache = _get_db(DB_PAGER_CACHE_KEY, {})
        self.skills = _get_db(DB_SKILLS_KEY, {})
        if isinstance(self.skills, list):
            self.skills = {f"skill_{i + 1}": str(v) for i, v in enumerate(self.skills)}
        elif not isinstance(self.skills, dict):
            self.skills = {}
        self.skills = {str(k): str(v) for k, v in self.skills.items()}
        # Провайдер храним в БД: конфиг Hikka иногда сбрасывается при перезапуске/обновлении.
        _saved_provider = _get_db(DB_PROVIDER_STATE_KEY, None)
        if (_saved_provider
                and _saved_provider in self.PROVIDER_SPECS
                and str(self.config.get("provider") or "").strip().lower() != _saved_provider):
            self.config["provider"] = _saved_provider
        if not self.api_keys and not any([self.config["openrouter_api_key"], self.config["huggingface_api_key"], self.config["openai_api_key"], self.config["deepseek_api_key"]]):
            logger.warning("magent: API ключи не настроены ни для одного провайдера.")
        global _gemini_log_client, _gemini_log_channel, _gemini_log_topic_id
        try:
            asset_channel = self._db.get("heroku.forums", "channel_id", 0)
            if asset_channel:
                notif_topic = await utils.asset_forum_topic(
                    self._client,
                    self._db,
                    asset_channel,
                    "magent Logs",
                    description="magent module warnings & errors.",
                    icon_emoji_id=5283176512747507510,
                )
                _gemini_log_client = self._client
                _gemini_log_channel = asset_channel
                _gemini_log_topic_id = notif_topic.id
        except Exception:
            pass

    # =========================================================================
    # Основные вспомогательные методы
    # =========================================================================

    def _clean_symbols_filter(self, text: str) -> str:
        """Заменяет все эмодзи (обычные Unicode и Telegram Premium <tg-emoji>/<emoji>)
        на строгие текстовые символы и Unicode-глифы из геометрических, технических и математических категорий."""
        if not text:
            return ""
        res = re.sub(r"<(?:tg-emoji|emoji)[^>]*>(.*?)</(?:tg-emoji|emoji)>", r"\1", str(text))
        mapping = {
            "🤖": "⌬", "📟": "⌬", "✨": "✦", "🔮": "◈", "🧠": "⏣",
            "▶️": "›", "➡️": "›", "◀️": "‹", "⌛️": "◴", "⌛": "◴", "⏱️": "◴", "⏱": "◴", "🕔": "◴", "⏳": "◴",
            "✅": "✓", "✔️": "✓", "✔": "✓", "❌": "✗", "✖️": "✗", "✖": "✗", "⛔": "▲", "🚫": "▲",
            "⚠️": "▲", "⚠": "▲", "❗️": "▲", "❗": "▲", "❕": "▲", "❓": "⍰", "🛠": "⎈", "🔧": "⎈",
            "💳": "◈", "🪙": "◈", "📌": "⌖", "🏷": "⌑", "💬": "»", "📝": "»",
            "🧹": "⌫", "🗑": "⌫", "🎭": "⍟", "🌐": "⬡", "🔗": "⤻",
            "📎": "⌑", "💾": "⎙", "🎨": "⬠", "🎵": "♫", "🔑": "⚿",
            "📊": "∷", "📈": "∷", "🧩": "◈", "⚛️": "⌬", "⚛": "⌬", "🧬": "⏣",
            "🟢": "●", "🟡": "◐", "🔴": "○", "▫️": "∅", "◽️": "∅", "🔄": "↺",
            "🚀": "»", "⚡️": "⌁", "⚡": "⌁", "🦖": "⌬", "💻": "⌨", "🤗": "⌬",
            "👁": "⌕", "👀": "⌕", "🔥": "✦", "💡": "✦", "🔍": "⌕", "🔎": "⌕",
            "🎯": "⌖", "🧭": "⌖", "📦": "∅", "💎": "◈", "👻": "◇", "💸": "◈",
            "📜": "⌗", "📖": "⌗", "🗂": "⌗", "🪐": "⬡", "🎤": "♫", "➕": "+",
            "👇": "▼", "👆": "▲", "ℹ️": "⌕", "ℹ": "⌕", "🌍": "◎",
            "👍": "✓", "👎": "✗", "👌": "✓", "🎉": "✦", "⭐": "✦", "🌟": "✦"
        }
        for emo, sym in mapping.items():
            res = res.replace(emo, sym)
        re_emojis = re.compile(
            r"[\U0001F300-\U0001F337\U0001F339-\U0001FAFF]|[\U0001F600-\U0001F64F]|[\U0001F680-\U0001F6FF]"
        )
        res = re_emojis.sub("", res)
        res = res.replace("\uFE0F", "").replace("\u200D", "")
        res = res.replace("▪", "∅").replace("▫", "∅").replace("▸", "∅").replace("■", "∅").replace("□", "∅")
        return res

    def _maybe_clean_symbols(self, text: str) -> str:
        """Применяет фильтр очистки эмодзи, если активен режим clean_symbols_mode."""
        if self.config.get("clean_symbols_mode", False):
            return self._clean_symbols_filter(text)
        return text

    def _skills_block(self) -> str:
        """Постоянные навыки/знания — инжектятся в системный промпт каждого запроса."""
        if not self.skills:
            return ""
        lines = ["<permanent_skills>", "The following are permanent learned skills and knowledge. Always apply them:"]
        for name, content in self.skills.items():
            lines.append(f"[skill: {name}]\n{content}")
        lines.append("</permanent_skills>")
        return "\n\n".join(lines)

    def _normalize_provider_name(self, provider: str = None) -> str:
        provider = str(provider or self.config["provider"] or "google").strip().lower()
        return {
            "gemini": "google", "google": "google",
            "or": "openrouter", "openrouter": "openrouter",
            "hf": "huggingface", "huggingface": "huggingface",
            "oa": "openai", "openai": "openai",
            "ds": "deepseek", "deepseek": "deepseek",
            "groq": "groq",
            "mistral": "mistral", "mixtral": "mistral",
            "together": "together", "togetherai": "together",
            "cerebras": "cerebras",
            "xai": "xai", "grok": "xai",
            "nvidia": "nvidia", "nim": "nvidia",
            "custom": "custom", "local": "custom",
        }.get(provider, provider)

    def _provider_spec(self, provider: str = None) -> dict:
        return self.PROVIDER_SPECS.get(self._normalize_provider_name(provider), self.PROVIDER_SPECS["google"])

    def _provider_label(self, provider: str = None) -> str:
        if self._normalize_provider_name(provider) == "custom":
            return str(self.config.get("custom_label") or "Custom")
        return self._provider_spec(provider).get("label", "Gemini")

    def _provider_default_model(self, provider: str = None) -> str:
        return self._provider_spec(provider).get("default_model", "gemini-3-flash-preview")

    def _save_provider_models(self):
        self.db.set(self.strings["name"], DB_PROVIDER_MODELS_KEY, self.provider_models)

    def _provider_model_entry(self, provider: str = None) -> dict:
        provider = self._normalize_provider_name(provider)
        entry = self.provider_models.get(provider, "")
        if isinstance(entry, dict):
            return {
                "model": str(entry.get("model") or "").strip(),
                "manual": bool(entry.get("manual", True)),
                "profile": str(entry.get("profile") or "manual").strip().lower(),
                "auto_model": bool(entry.get("auto_model", False)),
            }
        value = str(entry or "").strip()
        return {"model": value, "manual": bool(value), "profile": "manual", "auto_model": False}

    def _remember_provider_model(self, provider: str = None, model_name: str = None, manual: bool = None):
        provider = self._normalize_provider_name(provider)
        if provider not in self.PROVIDER_SPECS:
            return
        model_name = str(model_name or self.config.get("model_name") or "").strip()
        if not model_name:
            return
        if manual is None:
            manual = (not self.config.get("auto_model", False)) or str(self.config.get("model_profile") or "").lower() == "manual"
        self.provider_models[provider] = {
            "model": model_name,
            "manual": bool(manual),
            "profile": str(self.config.get("model_profile") or ("manual" if manual else "auto")).strip().lower(),
            "auto_model": bool(self.config.get("auto_model", False)) if not manual else False,
        }
        self._save_provider_models()

    def _restore_provider_model(self, provider: str) -> str:
        provider = self._normalize_provider_name(provider)
        entry = self._provider_model_entry(provider)
        saved = entry.get("model")
        if saved:
            self.config["model_name"] = saved
            self.config["auto_model"] = bool(entry.get("auto_model", False)) if not entry.get("manual", True) else False
            profile = str(entry.get("profile") or "manual").lower()
            self.config["model_profile"] = profile if profile in MODEL_PROFILE_CHOICES else "manual"
            return saved
        default = self._provider_default_model(provider)
        self.config["model_name"] = default
        return default

    def _provider_profile_models(self, provider: str = None) -> dict:
        provider = self._normalize_provider_name(provider)
        profiles = dict(self._provider_spec(provider).get("profiles", {}) or {})
        default = self._provider_default_model(provider)
        profiles.setdefault("auto", default)
        profiles.setdefault("balanced", default)
        profiles.setdefault("manual", self.config.get("model_name") or default)
        return profiles

    def _provider_curated_models(self, provider: str = None) -> list:
        provider = self._normalize_provider_name(provider)
        models = list(self._provider_spec(provider).get("fallback_models", ()) or ())
        if provider == "custom":
            cust = str(self.config.get("custom_model") or "").strip()
            if cust:
                models.append(cust)
            else:
                models.append("gpt-4o")
        return list(dict.fromkeys([str(model).strip() for model in models if str(model).strip()]))

    def _google_model_candidates(self, primary: str, limit: int = 5) -> list:
        """Основная модель + дешёвые фолбэки (для авто-перехода при дневной квоте модели)."""
        cands = [str(primary).strip()] if primary else []
        for m in self._provider_spec("google").get("fallback_models", ()):
            m = str(m).strip()
            if m and m not in cands:
                cands.append(m)
        return cands[:limit] or [str(primary or "gemini-2.5-flash")]

    def _model_matches_provider(self, model_name: str, provider: str) -> bool:
        model = str(model_name or "").strip().lower()
        provider = self._normalize_provider_name(provider)
        if not model:
            return True
        if provider != "google" and any(model.startswith(p) for p in ("gemini-", "imagen-", "veo-", "lyria-")):
            return False
        if provider in ("groq", "mistral", "together", "cerebras", "xai", "nvidia", "custom"):
            return True
        cached = getattr(self, "_provider_models_api_cache", {}).get(provider, {}).get("models", [])
        if any(model == str(m).strip().lower() for m in cached):
            return True
        if provider == "google":
            return any(model.startswith(p) for p in self.PROVIDER_SPECS["google"]["model_prefixes"]) and "/" not in model
        if provider == "openrouter":
            return "/" in model or any(model.startswith(p) for p in self.PROVIDER_SPECS["openrouter"]["model_prefixes"])
        if provider == "huggingface":
            return "/" in model or any(model.startswith(p) for p in self.PROVIDER_SPECS["huggingface"]["model_prefixes"])
        if provider == "openai":
            return any(model.startswith(p) for p in self.PROVIDER_SPECS["openai"]["model_prefixes"]) and "/" not in model
        if provider == "deepseek":
            return any(model.startswith(p) for p in self.PROVIDER_SPECS["deepseek"]["model_prefixes"]) and "/" not in model
        return False

    def _parts_have_image_like_media(self, parts: list) -> bool:
        for part in parts or []:
            inline = getattr(part, "inline_data", None)
            if not inline:
                continue
            mime = str(getattr(inline, "mime_type", "") or "").lower()
            if mime.startswith(("image/", "video/")):
                return True
        return False

    def _guess_model_profile_from_request(self, parts: list, request_text: str = "") -> str:
        if self._parts_have_image_like_media(parts):
            return "vision"
        text = str(request_text or "")
        for part in parts or []:
            if getattr(part, "text", None):
                text += "\n" + str(part.text)
        low = text.lower()
        if any(h in low for h in ("код", "скрипт", "traceback", "stack trace", "python", "javascript", "typescript", "api", "regex", "pytest", "docker")):
            return "coding"
        if any(h in low for h in ("объясни", "проанализируй", "сравни", "докажи", "архитектур", "reason", "solve", "proof")):
            return "reasoning"
        return "balanced"

    def _resolve_effective_model(self, provider: str, configured_model: str = None, parts: list = None, request_text: str = "") -> str:
        provider = self._normalize_provider_name(provider)
        provider_config_keys = self.PROVIDER_MODEL_CFG
        cfg_key = provider_config_keys.get(provider, "")
        provider_model = str(self.config.get(cfg_key, "") if cfg_key else "").strip()
        default = self._provider_default_model(provider)
        configured = ""
        if provider_model and self._model_matches_provider(provider_model, provider):
            configured = provider_model
        elif configured_model and self._model_matches_provider(configured_model, provider):
            configured = configured_model
        elif provider == "google":
            glob = str(self.config.get("model_name") or "").strip()
            if glob and self._model_matches_provider(glob, provider):
                configured = glob
        if not self.config.get("auto_model", False):
            return configured or default
        profile = str(self.config.get("model_profile") or "auto").strip().lower()
        if profile not in MODEL_PROFILE_CHOICES:
            profile = "auto"
        if profile == "manual":
            return configured or default
        selected = self._guess_model_profile_from_request(parts or [], request_text) if profile == "auto" else profile
        profiles = self._provider_profile_models(provider)
        return profiles.get(selected) or profiles.get("balanced") or configured or default

    def _extract_request_text_for_display(self, parts: list, fallback: str = None) -> str:
        if fallback:
            return fallback
        chunks = []
        for part in parts or []:
            text = getattr(part, "text", None)
            if text:
                chunks.append(str(text))
        return "\n".join(chunks).strip() or "[медиа-запрос]"

    def _human_duration(self, seconds: float) -> str:
        seconds = int(max(0, seconds))
        d, rem = divmod(seconds, 86400)
        h, rem = divmod(rem, 3600)
        m, s = divmod(rem, 60)
        parts = []
        if d: parts.append(f"{d}д")
        if h: parts.append(f"{h}ч")
        if m: parts.append(f"{m}м")
        parts.append(f"{s}с")
        return " ".join(parts)

    def _record_session_usage(self, tokens_in: int = 0, tokens_out: int = 0, elapsed: float = 0.0, provider: str = None):
        self.session_stats["requests"] = int(self.session_stats.get("requests", 0) or 0) + 1
        self.session_stats["tokens_in"] = int(self.session_stats.get("tokens_in", 0) or 0) + int(tokens_in or 0)
        self.session_stats["tokens_out"] = int(self.session_stats.get("tokens_out", 0) or 0) + int(tokens_out or 0)
        if provider:
            bp = self.session_stats.setdefault("by_provider", {})
            p = bp.setdefault(provider, {"requests": 0, "tokens": 0})
            p["requests"] = int(p.get("requests", 0)) + 1
            p["tokens"] = int(p.get("tokens", 0)) + int(tokens_in or 0) + int(tokens_out or 0)
        times = list(self.session_stats.get("times", []) or [])
        times.append(float(elapsed or 0))
        self.session_stats["times"] = times[-200:]
        self.db.set(self.strings["name"], DB_SESSION_STATS_KEY, {
            "requests": self.session_stats["requests"],
            "tokens_in": self.session_stats["tokens_in"],
            "tokens_out": self.session_stats["tokens_out"],
                "times": self.session_stats["times"],
                "by_provider": self.session_stats.get("by_provider", {}),
            })

    def _model_info_line(self, provider: str, model: str, elapsed: float = 0.0, tokens_in: int = 0, tokens_out: int = 0) -> str:
        extra = ""
        if self.config.get("show_time", True):
            extra += f" ◴ {round(float(elapsed or 0), 1)}с"
        if self.config.get("show_tokens", True) and (tokens_in or tokens_out):
            extra += f" ◈ {int(tokens_in or 0) + int(tokens_out or 0)}"
        return f"<i>⌬ {self._provider_label(provider)}: <code>{utils.escape_html(str(model))}</code>{extra}</i>"

    def _extract_retry_delay_seconds(self, text: str, default: int = 3600) -> int:
        raw = str(text or "")
        match = re.search(r"retryDelay['\"]?\s*[:=]\s*['\"]?(\d+)s", raw, flags=re.IGNORECASE)
        if match:
            return max(60, min(int(match.group(1)), 86400))
        match = re.search(r"retry after\s+(\d+)", raw, flags=re.IGNORECASE)
        if match:
            return max(60, min(int(match.group(1)), 86400))
        return default

    def _set_key_cooldown(self, key: str, seconds: int):
        if key:
            self.key_cooldowns[str(key)] = time.time() + max(60, int(seconds or 3600))

    def _get_openrouter_keys(self) -> list:
        raw = str(self.config.get("openrouter_api_key") or "")
        return [key.strip() for key in raw.split(",") if key.strip()]

    def _get_huggingface_keys(self) -> list:
        raw = str(self.config.get("huggingface_api_key") or "")
        return [key.strip() for key in raw.split(",") if key.strip()]

    def _get_openai_keys(self) -> list:
        raw = str(self.config.get("openai_api_key") or "")
        return [key.strip() for key in raw.split(",") if key.strip()]

    def _get_deepseek_keys(self) -> list:
        raw = str(self.config.get("deepseek_api_key") or "")
        return [key.strip() for key in raw.split(",") if key.strip()]

    def _get_proxy_config(self):
        p = self.config["proxy"]
        return {"http://": p, "https://": p} if p else None

    # =========================================================================
    # Работа с памятью
    # =========================================================================

    def _save_history_sync(self, gauto: bool=False):
        if getattr(self, "_db_broken", False): return
        data, key = (self.gauto_conversations, DB_GAUTO_HISTORY_KEY) if gauto else (self.conversations, DB_HISTORY_KEY)
        try: self.db.set(self.strings["name"], key, data)
        except: self._db_broken = True

    def _load_history_from_db(self, key):
        d = self.db.get(self.strings["name"], key, None)
        if (d is None or not d) and self.strings["name"] != "Gemini":
            d = self.db.get("Gemini", key, {})
        return d if isinstance(d, dict) else {}

    def _get_structured_history(self, cid, gauto=False):
        d = self.gauto_conversations if gauto else self.conversations
        if str(cid) not in d: d[str(cid)] = []
        return d[str(cid)]

    def _is_memory_enabled(self, chat_id: str) -> bool:
        return chat_id not in self.memory_disabled_chats

    def _update_history(self, chat_id: int, user_parts: list, model_response: str, regeneration: bool = False, message: Message = None, gauto: bool = False):
        if not self._is_memory_enabled(str(chat_id)):
            return
        history = self._get_structured_history(chat_id, gauto)
        now = int(time.time())
        user_id = self.me.id
        message_id = getattr(message, "id", None)
        if message:
            try:
                peer_id = get_peer_id(message)
                if peer_id:
                    user_id = peer_id
            except (TypeError, ValueError):
                if message.sender_id: user_id = message.sender_id

        user_text = " ".join([p.text for p in user_parts if hasattr(p, "text") and p.text]) or "[ответ на медиа]"

        if regeneration and history:
            for i in range(len(history) - 1, -1, -1):
                if history[i].get("role") == "model":
                    history[i].update({"content": model_response, "date": now})
                    break
        else:
            user_entry = {
                "role": "user", "type": "text", "content": user_text,
                "date": now, "user_id": user_id, "message_id": message_id
            }
            model_entry = {
                "role": "model", "type": "text", "content": model_response,
                "date": now, "user_id": None
            }
            history.extend([user_entry, model_entry])

        limit = self.config["max_history_length"]
        if limit > 0 and len(history) > limit * 2:
            history = history[-(limit * 2):]

        target = self.gauto_conversations if gauto else self.conversations
        target[str(chat_id)] = history
        self._save_history_sync(gauto)

    def _clear_history(self, cid, gauto=False):
        d = self.gauto_conversations if gauto else self.conversations
        if str(cid) in d:
            del d[str(cid)]
            self._save_history_sync(gauto)

    # =========================================================================
    # Форматирование и UI
    # =========================================================================

    def _markdown_to_html(self, text: str) -> str:
        text = re.sub(r"<think>.*?</think>", "", text, flags=re.DOTALL)
        text = re.sub(r"<thought>.*?</thought>", "", text, flags=re.DOTALL)
        text = re.sub(r"(?i)<br\s*/?>", "\n", text)
        def heading_replacer(m):
            level = len(m.group(1))
            title = m.group(2).strip()
            indent = "   " * (level - 1)
            return f"{indent}<b>{title}</b>"
        text = re.sub(r"^(#+)\s+(.*)", heading_replacer, text, flags=re.M)
        def list_replacer(m):
            return f"{m.group(1)}• "
        text = re.sub(r"^([ \t]*)[-*+]\s+", list_replacer, text, flags=re.M)
        md = MarkdownIt("commonmark", {"html": True, "linkify": True})
        md.enable("strikethrough")
        md.disable("hr"); md.disable("heading"); md.disable("list")
        html_text = md.render(text)
        def format_code(match):
            lang = utils.escape_html(match.group(1).strip())
            code = utils.escape_html(match.group(2).strip())
            return f'<pre><code class="language-{lang}">{code}</code></pre>' if lang else f'<pre><code>{code}</code></pre>'
        html_text = re.sub(r"```(.*?)\n([\s\S]+?)\n```", format_code, html_text)
        html_text = re.sub(r"<p>(<pre>[\s\S]*?</pre>)</p>", r"\1", html_text, flags=re.DOTALL)
        html_text = html_text.replace("<p>", "").replace("</p>", "\n")
        html_text = re.sub(r"(?i)<br\s*/?>", "\n", html_text).strip()
        return html_text

    def _format_response_with_smart_separation(self, text: str) -> str:
        pattern = r"(<pre.*?>[\s\S]*?</pre>)"
        parts = re.split(pattern, text, flags=re.DOTALL)
        result_parts = []
        for i, part in enumerate(parts):
            if not part or part.isspace():
                continue
            if i % 2 == 1:
                result_parts.append(part.strip())
            else:
                stripped_part = part.strip()
                if stripped_part:
                    result_parts.append(f'<blockquote expandable="true">{stripped_part}</blockquote>')
        return "\n".join(result_parts)

    def _paginate_text(self, text: str, limit: int) -> list:
        pages = []
        current_page_lines = []
        current_len = 0
        in_code_block = False
        current_code_lang = ""
        lines = text.split('\n')
        for line in lines:
            line_len = len(line) + 1
            stripped = line.strip()
            if stripped.startswith("```"):
                if in_code_block:
                    in_code_block = False
                    current_code_lang = ""
                else:
                    in_code_block = True
                    current_code_lang = stripped.replace("```", "").strip()
            if current_len + line_len > limit and current_page_lines:
                if in_code_block: current_page_lines.append("```")
                pages.append("\n".join(current_page_lines))
                current_page_lines = []
                current_len = 0
                if in_code_block:
                    header = f"```{current_code_lang}"
                    current_page_lines.append(header)
                    current_len += len(header) + 1
            current_page_lines.append(line)
            current_len += line_len
        if current_page_lines:
            pages.append("\n".join(current_page_lines))
        return pages

    def _get_inline_buttons(self, chat_id, base_message_id):
        return [[
            {"text": self.strings["btn_clear"], "callback": self._clear_callback, "args": (chat_id,)},
            {"text": self.strings["btn_regenerate"], "data": f"gemini:regen:{chat_id}:{base_message_id}"}
        ]]

    async def _render_page(self, uid, page_num, entity):
        data = self.pager_cache.get(uid)
        if not data:
            if isinstance(entity, InlineCall):
                await entity.edit(
                    "▲ <b>Сессия истекла или бот был перезагружен с потерей данных.</b>",
                    reply_markup=[[{"text": "⌫ Удалить", "data": f"gemini:close:{uid}"}]]
                )
            return
        chunks = data["chunks"]
        total = data["total"]
        header = data.get("header", "")
        chat_id = data.get("chat_id")
        base_msg_id = data.get("msg_id")
        raw_text_chunk = chunks[page_num]
        safe_text = self._markdown_to_html(raw_text_chunk)
        formatted_body = self._format_response_with_smart_separation(safe_text)
        text_to_show = f"{header}\n{formatted_body}"
        text_to_show = text_to_show.replace('<emoji document_id=', '<tg-emoji emoji-id=').replace('</emoji>', '</tg-emoji>')
        nav_row = []
        if page_num > 0:
            nav_row.append({"text": "◀️", "data": f"gemini:pg:{uid}:{page_num - 1}"})
        nav_row.append({"text": f"{page_num + 1}/{total}", "data": "gemini:noop"})
        if page_num < total - 1:
            nav_row.append({"text": "▶️", "data": f"gemini:pg:{uid}:{page_num + 1}"})
        extra_row = [{"text": "✗ Закрыть", "data": f"gemini:close:{uid}"}]
        if chat_id and base_msg_id:
            extra_row.append({"text": "↺", "data": f"gemini:regen:{chat_id}:{base_msg_id}"})
        buttons = [nav_row, extra_row]
        if isinstance(entity, Message):
            await self.inline.form(text=text_to_show, message=entity, reply_markup=buttons)
        elif isinstance(entity, InlineCall):
            await entity.edit(text=text_to_show, reply_markup=buttons)
        elif hasattr(entity, "edit"):
            try: await entity.edit(text=text_to_show, reply_markup=buttons)
            except: pass

    async def _clear_callback(self, call: InlineCall, cid):
        hist_key = "global_context" if self.config["global_memory"] else cid
        self._clear_history(hist_key, gauto=False)
        await call.edit(self.strings["memory_cleared_global"] if hist_key == "global_context" else self.strings["memory_cleared"], reply_markup=None)

    async def _regenerate_callback(self, call: InlineCall, mid, cid):
        key = f"{cid}:{mid}"
        if key not in self.last_requests: return await call.answer(self.strings["no_last_request"], show_alert=True)
        parts, disp = self.last_requests[key]
        use_url_context = bool(re.search(r'https?://\S+', disp or ""))
        await self._send_to_gemini(mid, parts, regeneration=True, call=call, chat_id_override=cid, display_prompt=disp, use_url_context=use_url_context)

    # =========================================================================
    # API запросы
    # =========================================================================

    async def _send_to_gemini(self, message, parts: list, regeneration: bool=False, call: InlineCall=None, status_msg=None, chat_id_override: int=None, impersonation_mode: bool=False, use_url_context: bool=False, display_prompt: str=None, attempt: int = 1, is_retry: bool = False, ephemeral: bool = False): 
        msg_obj = None
        if regeneration or is_retry:
            chat_id = chat_id_override
            base_message_id = message
            try: msg_obj = await self.client.get_messages(chat_id, ids=base_message_id)
            except Exception: msg_obj = None
        else:
            chat_id = utils.get_chat_id(message)
            base_message_id = message.id
            msg_obj = message

        self._current_tool_chat_id = chat_id
        self._current_tool_message = msg_obj

        provider = self._normalize_provider_name()
        is_global = self.config["global_memory"] and not impersonation_mode
        history_key = "global_context" if is_global else str(chat_id)

        if regeneration or is_retry:
            current_turn_parts, request_text_for_display = self.last_requests.get(f"{chat_id}:{base_message_id}", (parts, "[регенерация]"))
        else:
            current_turn_parts = parts
            request_text_for_display = self._extract_request_text_for_display(parts, display_prompt)
            self.last_requests[f"{chat_id}:{base_message_id}"] = (current_turn_parts, request_text_for_display)

        target_model = self._resolve_effective_model(provider, self.config["model_name"], current_turn_parts, request_text_for_display)

        # --- OpenAI-compatible providers (всё, кроме нативного google) ---
        if provider != "google":
            return await self._handle_openai_compatible(
                provider, target_model, history_key, current_turn_parts, 
                request_text_for_display, regeneration, impersonation_mode, 
                chat_id, base_message_id, call, status_msg, attempt, ephemeral, msg_obj
            )

        # --- Google native ---
        return await self._handle_google_native(
            target_model, history_key, current_turn_parts, 
            request_text_for_display, regeneration, impersonation_mode, 
            chat_id, base_message_id, call, status_msg, attempt, ephemeral, msg_obj, use_url_context
        )

    async def _handle_openai_compatible(self, provider, target_model, history_key, current_turn_parts, request_text_for_display, regeneration, impersonation_mode, chat_id, base_message_id, call, status_msg, attempt, ephemeral, msg_obj):
        try:
            sys_instruct = self.config["system_instruction"] or None
            if impersonation_mode:
                my_name = get_display_name(self.me)
                chat_history_text = await self._get_recent_chat_text(chat_id)
                sys_instruct = self.config["impersonation_prompt"].format(my_name=my_name, chat_history=chat_history_text)

            _skills_block = self._skills_block()
            if _skills_block:
                sys_instruct = ((str(sys_instruct) + "\n\n") if sys_instruct else "") + _skills_block

            raw_hist = self._get_structured_history(history_key, gauto=impersonation_mode)
            if regeneration and raw_hist: raw_hist = raw_hist[:-2]
            openai_messages = self._convert_google_history_to_openai(raw_hist, sys_instruct)
            
            content_list = self._process_parts_for_openai(current_turn_parts, request_text_for_display)
            openai_messages.append({"role": "user", "content": content_list})

            tools_enabled = bool(self.config["enable_tools"]) and not impersonation_mode
            if tools_enabled:
                preamble = self._tools_system_preamble()
                if openai_messages and openai_messages[0].get("role") == "system":
                    openai_messages[0]["content"] = preamble + "\n\n" + str(openai_messages[0]["content"])
                else:
                    openai_messages.insert(0, {"role": "system", "content": preamble})

            _t_start = time.time()

            if tools_enabled:
                result_text, _tokens_in, _tokens_out = await self._run_openai_tool_loop(
                    provider, target_model, openai_messages, self._openai_tool_schema(),
                    self.config["temperature"], status_msg, call
                )
                _elapsed = round(time.time() - _t_start, 1)
            else:
                result_text, usage = await self._dispatch_openai(provider, target_model, openai_messages, self.config["temperature"])
                _elapsed = round(time.time() - _t_start, 1)
                _tokens_in = int(usage.get("prompt_tokens") or usage.get("input_tokens") or 0)
                _tokens_out = int(usage.get("completion_tokens") or usage.get("output_tokens") or 0)
            
            result_text = result_text.strip()
            result_text = re.sub(r"^\[System Info:.*?\]\s*", "", result_text, flags=re.IGNORECASE)
            result_text = re.sub(r"^\[\d{2}\.\d{2}\.\d{4} \d{2}:\d{2}\]\s*(?:Gemini:|Model:|Ассистент:|AI:)?\s*", "", result_text, flags=re.IGNORECASE)
            result_text = re.sub(r"^\[\d{2}:\d{2}\]\s*(?:Gemini:|Model:|Ассистент:|AI:)?\s*", "", result_text, flags=re.IGNORECASE)
            
            if not impersonation_mode:
                self._record_session_usage(_tokens_in, _tokens_out, _elapsed, provider=provider)
            if self._is_memory_enabled(str(chat_id)) and not ephemeral:
                self._update_history(history_key, current_turn_parts, result_text, regeneration, msg_obj, gauto=impersonation_mode)
            
            if impersonation_mode:
                return result_text
            
            return await self._format_final_response(
                chat_id, base_message_id, request_text_for_display, result_text,
                provider, target_model, _elapsed, _tokens_in, _tokens_out,
                history_key, call, status_msg, attempt
            )
        except Exception as e:
            return await self._handle_api_error(
                e, impersonation_mode, call, status_msg, chat_id, base_message_id, regeneration, attempt
            )

    async def _handle_google_native(self, target_model, history_key, current_turn_parts, request_text_for_display, regeneration, impersonation_mode, chat_id, base_message_id, call, status_msg, attempt, ephemeral, msg_obj, use_url_context: bool = False):
        api_keys_to_use = self._get_sorted_keys()
        if not api_keys_to_use:
            if not impersonation_mode and status_msg:
                await utils.answer(status_msg, self.strings['no_api_key'])
            return None if impersonation_mode else ""

        if impersonation_mode:
            my_name = get_display_name(self.me)
            chat_history_text = await self._get_recent_chat_text(chat_id)
            sys_instruct = self.config["impersonation_prompt"].format(my_name=my_name, chat_history=chat_history_text)
        else:
            sys_val = self.config["system_instruction"]
            sys_instruct = (sys_val.strip() if isinstance(sys_val, str) else "") or None

        _skills_block = self._skills_block()
        if _skills_block:
            sys_instruct = ((str(sys_instruct) + "\n\n") if sys_instruct else "") + _skills_block

        contents = self._prepare_google_contents(history_key, impersonation_mode, regeneration)
        time_parts = list(current_turn_parts)
        if not impersonation_mode:
            try:
                user_timezone = pytz.timezone(self.config["timezone"])
            except pytz.UnknownTimeZoneError:
                user_timezone = pytz.utc
            now = datetime.now(user_timezone)
            time_note = f"[System Info: Current local time is {now.strftime('%Y-%m-%d %H:%M:%S %Z')}]"
            if time_parts and getattr(time_parts[0], 'text', None):
                time_parts[0] = types.Part(text=f"{time_note}\n\n{time_parts[0].text}")
            else:
                time_parts.insert(0, types.Part(text=time_note))
        contents.append(types.Content(role="user", parts=time_parts))

        tools_enabled = bool(self.config["enable_tools"]) and not impersonation_mode
        tools = []
        if tools_enabled:
            # function-calling нельзя совмещать с google_search в одном запросе
            tools.append(self._tool_declarations())
            preamble = self._tools_system_preamble()
            sys_instruct = (preamble + "\n\n" + sys_instruct) if sys_instruct else preamble
        elif self.config["google_search"] or use_url_context:
            tools.append(types.Tool(google_search=types.GoogleSearch()))

        gen_config = types.GenerateContentConfig(
            temperature=self.config["temperature"],
            system_instruction=sys_instruct,
            tools=tools if tools else None,
            safety_settings=[
                types.SafetySetting(category=cat, threshold="BLOCK_NONE") 
                for cat in ["HARM_CATEGORY_HARASSMENT", "HARM_CATEGORY_HATE_SPEECH", "HARM_CATEGORY_SEXUALLY_EXPLICIT", "HARM_CATEGORY_DANGEROUS_CONTENT"]
            ]
        )
        proxy_config = self._get_proxy_config()

        _t_start = time.time()
        result_text = ""
        last_error = None
        was_successful = False
        _tokens_in = 0
        _tokens_out = 0
        max_retries = len(api_keys_to_use)
        model_candidates = self._google_model_candidates(target_model)
        active_model = target_model

        for active_model in model_candidates:
            model_exhausted = False
            for i in range(max_retries):
                api_key = api_keys_to_use[i]
                try:
                    http_opts = None
                    if proxy_config:
                        http_opts = types.HttpOptions(async_client_args={"proxies": proxy_config})
                    client = genai.Client(api_key=api_key, http_options=http_opts)
                    response = await client.aio.models.generate_content(
                        model=active_model,
                        contents=contents,
                        config=gen_config
                    )
                    if getattr(response, "usage_metadata", None):
                        _tokens_in += getattr(response.usage_metadata, "prompt_token_count", 0) or 0
                        _tokens_out += getattr(response.usage_metadata, "candidates_token_count", 0) or 0
                    if tools_enabled and self._response_has_function_call(response):
                        response, _ti, _to = await self._run_google_tool_loop(
                            client, active_model, contents, gen_config, response, status_msg, call
                        )
                        _tokens_in += _ti
                        _tokens_out += _to
                    if response.text:
                        result_text = response.text
                        was_successful = True
                        break
                    else:
                        raise ValueError("Empty response")
                except Exception as e:
                    err_str = str(e).lower()
                    is_model_daily_quota = (
                        any(x in err_str for x in ["429", "resource_exhausted", "quota", "exhausted"])
                        and any(x in err_str for x in ["per_model_per_day", "requests_per_model_per_day", "per day", "perday", "model:"])
                    )
                    is_key_quota = (
                        any(x in err_str for x in ["quota", "exhausted", "429", "permission_denied", "api key not valid", "api_key_invalid", "client application"])
                        and "model" not in err_str
                    )
                    if is_key_quota:
                        self._set_key_cooldown(api_key, self._extract_retry_delay_seconds(str(e), 3600))
                        if any(x in err_str for x in ["permission_denied", "api key not valid", "api_key_invalid"]):
                            self.key_model_map[api_key] = -1
                        else:
                            self.key_model_map[api_key] = 0
                        self.db.set(self.strings["name"], DB_KEY_MAP_KEY, self.key_model_map)
                        if i == max_retries - 1:
                            last_error = RuntimeError(f"All keys exhausted or blocked. Last: {e}")
                        continue
                    if is_model_daily_quota:
                        # дневной лимит на эту модель — ключи не помогут, пробуем следующую модель (flash)
                        model_exhausted = True
                        last_error = RuntimeError(f"Дневная квота модели <code>{active_model}</code> исчерпана. {e}")
                        logger.warning(f"Gemini: daily quota for {active_model} exhausted, fallback to next model.")
                        break
                    if any(x in err_str for x in ["blocked", "403", "bad request", "400", "invalid_argument", "500", "503"]):
                        if i == max_retries - 1:
                            last_error = RuntimeError(f"Google API returned error. Last: {e}")
                        continue
                    else:
                        last_error = e
                        break
            if was_successful:
                break
            if not model_exhausted:
                break

        target_model = active_model

        _elapsed = round(time.time() - _t_start, 1)
        
        try:
            if not was_successful:
                raise last_error or RuntimeError("Unknown generation error")
            
            result_text = result_text.strip()
            result_text = re.sub(r"^\[System Info:.*?\]\s*", "", result_text, flags=re.IGNORECASE)
            result_text = re.sub(r"^\[\d{2}\.\d{2}\.\d{4} \d{2}:\d{2}\]\s*(?:Gemini:|Model:|Ассистент:|AI:)?\s*", "", result_text, flags=re.IGNORECASE)
            result_text = re.sub(r"^\[\d{2}:\d{2}\]\s*(?:Gemini:|Model:|Ассистент:|AI:)?\s*", "", result_text, flags=re.IGNORECASE)
            
            if not impersonation_mode:
                self._record_session_usage(_tokens_in, _tokens_out, _elapsed, provider="google")
            if self._is_memory_enabled(str(chat_id)) and not ephemeral:
                self._update_history(history_key, current_turn_parts, result_text, regeneration, msg_obj, gauto=impersonation_mode)
            
            if impersonation_mode:
                return result_text
            
            return await self._format_final_response(
                chat_id, base_message_id, request_text_for_display, result_text,
                "google", target_model, _elapsed, _tokens_in, _tokens_out,
                history_key, call, status_msg, attempt
            )
        except Exception as e:
            return await self._handle_api_error(
                e, impersonation_mode, call, status_msg, chat_id, base_message_id, regeneration, attempt
            )

    # =========================================================================
    # Инструменты-агент (function-calling)
    # =========================================================================

    def _tools_system_preamble(self) -> str:
        wd = self.config.get("tools_workdir") or "(текущая директория процесса)"
        return (
            "Ты — автономный CLI-агент внутри Telegram-юзербота владельца аккаунта. "
            "В твоём распоряжении полный набор инструментов для управления хостом, кодом, файлами, Telegram и интернетом:\n"
            "- run_terminal: выполнение любых shell-команд на хосте (bash/sh, git, python, curl, pip, docker и пр.)\n"
            "- read_file: чтение текстовых файлов с номерами строк и пагинацией (offset_lines, limit_lines)\n"
            "- write_file: создание или полная перезапись файлов на диске\n"
            "- search_in_file: умный поиск текста/регекса в файле с номерами строк и контекстом (grep)\n"
            "- find_files: поиск файлов по шаблону (glob) в директориях (*.py, *.json, bot*)\n"
            "- send_file: отправка файла пользователю в чат Telegram (готовый файл с диска path ИЛИ генерация кода/текста в файл content + filename)\n"
            "- replace_in_file: точечная замена блоков текста в файле без перезаписи всего файла\n"
            "- read_chat_file: чтение и скачивание файлов/документов/медиа из сообщений чата\n"
            "- list_dir: просмотр файлов и папок в директории\n"
            "- tg_send / tg_history: отправка сообщений и чтение истории Telegram-чатов\n"
            "- web_search / fetch_url: актуальный поиск в интернете (DuckDuckGo) и чтение веб-страниц\n"
            "- save_skill: сохранение важного факта/навыка в долговременную память (помнится всегда)\n\n"
            "Правила работы:\n"
            "1. Заметив важный факт о пользователе или его предпочтениях — сразу сохраняй через save_skill.\n"
            "2. Для актуальной информации используй web_search и fetch_url вместо догадок.\n"
            "3. Если пользователь просит отправить файл или написать скрипт/код/документ — используй send_file, чтобы отправить готовый файл прямо в Telegram!\n"
            "4. Действуй последовательно и пошагово, выполняя задачу до конца.\n"
            f"Рабочая директория: {wd}. Будь аккуратен с деструктивными действиями (rm -rf, дроп БД)."
        )

    def _tool_declarations(self):
        FD = types.FunctionDeclaration
        s = lambda d: {"type": "STRING", "description": d}
        i = lambda d: {"type": "INTEGER", "description": d}
        b = lambda d: {"type": "BOOLEAN", "description": d}
        decls = [
            FD(name="run_terminal",
               description="Выполнить shell-команду на хосте сервера и получить exit_code + stdout/stderr. Управление ботами, процессами, git, pip, файлами, системой.",
               parameters={"type": "OBJECT", "properties": {"command": s("Команда shell")}, "required": ["command"]}),
            FD(name="read_file",
               description="Прочитать текстовый файл с диска хоста с номерами строк и пагинацией.",
               parameters={"type": "OBJECT", "properties": {"path": s("Путь к файлу"), "offset_lines": i("С какой строки читать (1-indexed, по умолчанию 1)"), "limit_lines": i("Сколько строк читать (по умолчанию 200, макс 1000)")}, "required": ["path"]}),
            FD(name="write_file",
               description="Создать или перезаписать текстовый файл на диске хоста.",
               parameters={"type": "OBJECT", "properties": {"path": s("Путь к файлу"), "content": s("Полное содержимое файла")}, "required": ["path", "content"]}),
            FD(name="search_in_file",
               description="Поиск подстроки или регулярного выражения в файле с номерами строк и контекстом (grep).",
               parameters={"type": "OBJECT", "properties": {"path": s("Путь к файлу"), "query": s("Строка или regex для поиска"), "regex": b("Использовать регулярное выражение (True/False)"), "context_lines": i("Строк контекста вокруг совпадения (по умолчанию 2)")}, "required": ["path", "query"]}),
            FD(name="find_files",
               description="Поиск файлов по шаблону (glob) в директории (например: *.py, *.json, bot*).",
               parameters={"type": "OBJECT", "properties": {"path": s("Директория (по умолчанию '.')"), "pattern": s("Шаблон имени (по умолчанию '*')"), "max_results": i("Максимум результатов (по умолчанию 50)"), "recursive": b("Искать рекурсивно в подпапках (по умолчанию True)")}, "required": []}),
            FD(name="send_file",
               description="Отправить файл в Telegram-чат. Можно отправить готовый файл с диска (path) ИЛИ сгенерировать контент и отправить файлом (content + filename).",
               parameters={"type": "OBJECT", "properties": {"path": s("Путь к файлу на диске"), "content": s("Текст/код для отправки новым файлом"), "filename": s("Имя файла при отправке content (например script.py)"), "caption": s("Подпись к файлу"), "chat": s("ID чата, @username или me (по умолчанию текущий чат)")}, "required": []}),
            FD(name="replace_in_file",
               description="Точечная замена фрагмента текста в файле на новый без перезаписи всего файла.",
               parameters={"type": "OBJECT", "properties": {"path": s("Путь к файлу"), "old_text": s("Точный текст для замены"), "new_text": s("Новый текст для вставки")}, "required": ["path", "old_text", "new_text"]}),
            FD(name="read_chat_file",
               description="Прочитать или скачать файл/документ/фото из сообщения Telegram.",
               parameters={"type": "OBJECT", "properties": {"chat": s("ID чата или @username (по умолчанию текущий)"), "message_id": i("ID сообщения с файлом (по умолчанию отвеченное сообщение)")}, "required": []}),
            FD(name="list_dir",
               description="Показать содержимое директории на хосте.",
               parameters={"type": "OBJECT", "properties": {"path": s("Путь (по умолчанию текущая)")}, "required": []}),
            FD(name="tg_send",
               description="Отправить текстовое сообщение в Telegram-чат от имени владельца.",
               parameters={"type": "OBJECT", "properties": {"chat": s("id, @username или me"), "text": s("Текст сообщения")}, "required": ["chat", "text"]}),
            FD(name="tg_history",
               description="Получить последние сообщения из Telegram-чата. chat: id, @username или 'me'.",
               parameters={"type": "OBJECT", "properties": {"chat": s("id, @username или me"), "limit": i("Сколько сообщений (1-50)")}, "required": ["chat"]}),
            FD(name="web_search",
               description="Поиск в интернете (DuckDuckGo). Возвращает топ результатов: заголовок + ссылка + сниппет. Для актуальной информации.",
               parameters={"type": "OBJECT", "properties": {"query": s("Поисковый запрос")}, "required": ["query"]}),
            FD(name="fetch_url",
               description="Загрузить веб-страницу по URL и вернуть её текст (HTML очищается до читаемого текста).",
               parameters={"type": "OBJECT", "properties": {"url": s("URL страницы")}, "required": ["url"]}),
            FD(name="upload_file",
               description="Загрузить файл на публичный хостинг (x0.at, 0x0.st, catbox.moe) и получить прямую ссылку для скачивания. Можно указать path к файлу на диске ИЛИ content + filename.",
               parameters={"type": "OBJECT", "properties": {"path": s("Путь к файлу на диске"), "content": s("Текст/код для загрузки файлом"), "filename": s("Имя файла (например test.py)"), "service": s("Сервис: 'x0', '0x0' или 'catbox' (по умолчанию 'x0')")}, "required": []}),
            FD(name="tg_action",
               description="Системные действия в Telegram: pin_message, unpin_message, delete_messages, get_chat_info, get_user_info, search_messages, get_dialogs, mark_chat_read.",
               parameters={"type": "OBJECT", "properties": {"action": s("Действие: pin_message/unpin_message/delete_messages/get_chat_info/get_user_info/search_messages/get_dialogs/mark_chat_read"), "target": s("Чат или пользователь (id, @username или me)"), "message_ids": {"type": "ARRAY", "items": {"type": "INTEGER"}, "description": "ID сообщений для действия"}, "limit": i("Лимит (1-50)"), "query": s("Поисковый запрос для search_messages")}, "required": ["action"]}),
            FD(name="save_skill",
               description="Сохранить постоянный навык/факт в долговременную память (навык запоминается навсегда и применяется во всех будущих ответах).",
               parameters={"type": "OBJECT", "properties": {"name": s("Короткое имя навыка, латиницей, без пробелов"), "content": s("Текст навыка — что запомнить или как себя вести")}, "required": ["name", "content"]}),
        ]
        return types.Tool(function_declarations=decls)

    def _response_has_function_call(self, response) -> bool:
        try:
            for cand in (response.candidates or []):
                for p in (cand.content.parts or []):
                    if getattr(p, "function_call", None):
                        return True
        except Exception:
            pass
        return False

    def _extract_function_calls(self, response):
        cand = (response.candidates or [None])[0]
        calls = []
        if cand and getattr(cand, "content", None) and cand.content.parts:
            for p in cand.content.parts:
                fc = getattr(p, "function_call", None)
                if fc:
                    calls.append(fc)
        return calls, cand

    async def _run_google_tool_loop(self, client, model, contents, config, response, status_msg=None, call=None):
        ti = to = 0
        self._tool_steps = []
        self._tool_start_time = time.time()
        self._active_provider = "google"
        self._active_model = model
        out_limit = int(self.config["tools_output_limit"])
        for _ in range(int(self.config["tools_max_iters"])):
            calls, cand = self._extract_function_calls(response)
            if not calls:
                break
            if cand and getattr(cand, "content", None):
                contents.append(cand.content)
            resp_parts = []
            for fc in calls:
                args = dict(fc.args) if getattr(fc, "args", None) else {}
                out = await self._run_tool_step(status_msg, call, fc.name, args)
                resp_parts.append(types.Part.from_function_response(
                    name=fc.name, response={"result": str(out)[:out_limit]}
                ))
            contents.append(types.Content(role="user", parts=resp_parts))
            response = await client.aio.models.generate_content(model=model, contents=contents, config=config)
            um = getattr(response, "usage_metadata", None)
            if um:
                ti += getattr(um, "prompt_token_count", 0) or 0
                to += getattr(um, "candidates_token_count", 0) or 0
        return response, ti, to

    def _openai_tool_schema(self):
        def f(name, desc, props, required):
            return {"type": "function", "function": {
                "name": name, "description": desc,
                "parameters": {"type": "object", "properties": props, "required": required},
            }}
        s = lambda d: {"type": "string", "description": d}
        i = lambda d: {"type": "integer", "description": d}
        b = lambda d: {"type": "boolean", "description": d}
        return [
            f("run_terminal", "Выполнить shell-команду на хосте сервера и получить exit_code + stdout/stderr. Управление ботами, процессами, git, pip, файлами, системой.", {"command": s("Команда shell")}, ["command"]),
            f("read_file", "Прочитать текстовый файл с диска хоста с номерами строк и пагинацией.", {"path": s("Путь к файлу"), "offset_lines": i("С какой строки читать (1-indexed)"), "limit_lines": i("Сколько строк читать (макс 1000)")}, ["path"]),
            f("write_file", "Создать/перезаписать текстовый файл на диске хоста.", {"path": s("Путь"), "content": s("Содержимое")}, ["path", "content"]),
            f("search_in_file", "Поиск подстроки или regex в файле с номерами строк и контекстом (grep).", {"path": s("Путь к файлу"), "query": s("Что искать"), "regex": b("Regex (True/False)"), "context_lines": i("Строк контекста (по умолчанию 2)")}, ["path", "query"]),
            f("find_files", "Поиск файлов по шаблону (glob) в директории (например: *.py, *.json, bot*).", {"path": s("Директория (по умолчанию '.')"), "pattern": s("Шаблон имени (по умолчанию '*')"), "max_results": i("Максимум результатов"), "recursive": b("Рекурсивно (True/False)")}, []),
            f("send_file", "Отправить файл в Telegram-чат. Укажите path (файл на диске) ИЛИ content + filename (создать и отправить).", {"path": s("Путь к файлу на диске"), "content": s("Текст/код для отправки файлом"), "filename": s("Имя файла"), "caption": s("Подпись к файлу"), "chat": s("Чат (по умолчанию текущий)")}, []),
            f("replace_in_file", "Точечная замена фрагмента текста в файле на новый без перезаписи всего файла.", {"path": s("Путь к файлу"), "old_text": s("Точный текст для замены"), "new_text": s("Новый текст")}, ["path", "old_text", "new_text"]),
            f("read_chat_file", "Прочитать или скачать файл/документ/медиа из сообщения Telegram.", {"chat": s("ID чата (по умолчанию текущий)"), "message_id": i("ID сообщения (по умолчанию отвеченное)")}, []),
            f("upload_file", "Загрузить файл на публичный хостинг (x0.at, 0x0.st, catbox) и получить прямую ссылку. Передайте path ИЛИ content + filename.", {"path": s("Путь к файлу"), "content": s("Текст/код файла"), "filename": s("Имя файла"), "service": s("Хостинг ('x0', '0x0', 'catbox')")}, []),
            f("tg_action", "Системные действия в Telegram (pin_message, unpin_message, delete_messages, get_chat_info, get_user_info, search_messages, get_dialogs, mark_chat_read).", {"action": s("Действие"), "target": s("Чат/юзер (id, @username, me)"), "message_ids": {"type": "array", "items": {"type": "integer"}, "description": "ID сообщений"}, "limit": i("Лимит"), "query": s("Текст поиска")}, ["action"]),
            f("list_dir", "Показать содержимое директории на хосте.", {"path": s("Путь (по умолчанию текущая)")}, []),
            f("tg_send", "Отправить сообщение в Telegram-чат от имени владельца. chat: id, @username или 'me'.", {"chat": s("id, @username или me"), "text": s("Текст")}, ["chat", "text"]),
            f("tg_history", "Получить последние сообщения из Telegram-чата. chat: id, @username или 'me'.", {"chat": s("id, @username или me"), "limit": i("1-50")}, ["chat"]),
            f("web_search", "Поиск в интернете (DuckDuckGo): топ результатов (заголовок + ссылка + сниппет).", {"query": s("Поисковый запрос")}, ["query"]),
            f("fetch_url", "Загрузить веб-страницу по URL и вернуть её текст (HTML очищается).", {"url": s("URL страницы")}, ["url"]),
            f("save_skill", "Сохранить постоянный навык/факт в долговременную память (запоминается навсегда, применяется во всех будущих ответах).", {"name": s("Короткое имя навыка"), "content": s("Текст навыка")}, ["name", "content"]),
        ]

    _KNOWN_TOOLS = (
        "run_terminal", "read_file", "write_file", "search_in_file", "find_files",
        "send_file", "replace_in_file", "read_chat_file", "upload_file", "tg_action", "list_dir",
        "tg_send", "tg_history", "web_search", "fetch_url", "save_skill"
    )

    def _normalize_tool_call(self, tc):
        """Чинит кривые tool_call (напр. Groq склеивает имя с аргументами: 'run_terminal {"command": ...}')."""
        fn = tc.get("function", {}) or {}
        raw_name = str(fn.get("name", "") or "")
        raw_args = fn.get("arguments")
        name, embedded = raw_name.strip(), None
        m = re.match(r"\s*([A-Za-z_][\w]*)\s*(\{.*\})?\s*$", raw_name, re.S)
        if m:
            name = m.group(1)
            embedded = m.group(2)
        if name not in self._KNOWN_TOOLS:
            return None, {}, None
        args_src = raw_args if (raw_args not in (None, "", "{}")) else (embedded or "{}")
        try:
            args = json.loads(args_src) if isinstance(args_src, str) else (args_src or {})
        except Exception:
            args = {}
        if not isinstance(args, dict):
            args = {}
        fixed = {
            "id": tc.get("id") or f"call_{name}",
            "type": "function",
            "function": {"name": name, "arguments": json.dumps(args, ensure_ascii=False)},
        }
        return name, args, fixed

    def _first_json_obj(self, s, start=0):
        i = s.find("{", start)
        while i != -1:
            depth = 0
            for j in range(i, len(s)):
                if s[j] == "{":
                    depth += 1
                elif s[j] == "}":
                    depth -= 1
                    if depth == 0:
                        return s[i:j + 1]
            i = s.find("{", i + 1)
        return None

    def _parse_failed_generation(self, text):
        """Достаёт вызов инструмента из groq-поля failed_generation (модель сгенерила кривой формат)."""
        if not text:
            return []
        text = str(text)
        best = None
        for name in self._KNOWN_TOOLS:
            idx = text.find(name)
            if idx != -1 and (best is None or idx < best[0]):
                best = (idx, name)
        if not best:
            try:
                obj = json.loads(text)
            except Exception:
                obj = None
            if isinstance(obj, dict) and obj.get("name") in self._KNOWN_TOOLS:
                a = obj.get("arguments") or obj.get("parameters") or {}
                if isinstance(a, str):
                    try: a = json.loads(a)
                    except Exception: a = {}
                return [(obj["name"], a if isinstance(a, dict) else {})]
            return []
        idx, name = best
        blob = self._first_json_obj(text, idx + len(name)) or self._first_json_obj(text, 0)
        args = {}
        if blob:
            try:
                obj = json.loads(blob)
                if isinstance(obj, dict) and ("arguments" in obj or "parameters" in obj):
                    a = obj.get("arguments") or obj.get("parameters") or {}
                    args = json.loads(a) if isinstance(a, str) else (a or {})
                elif isinstance(obj, dict):
                    args = obj
            except Exception:
                args = {}
        return [(name, args if isinstance(args, dict) else {})]

    async def _run_openai_tool_loop(self, provider, model, messages, tools, temperature, status_msg=None, call=None):
        ti = to = 0
        self._tool_steps = []
        self._tool_start_time = time.time()
        self._active_provider = provider
        self._active_model = model
        out_limit = int(self.config["tools_output_limit"])
        final_text = ""
        for _ in range(int(self.config["tools_max_iters"]) + 1):
            try:
                msg_obj, usage = await self._dispatch_openai(provider, model, messages, temperature, tools)
            except Exception as e:
                # модель сгенерила кривой tool-call → пробуем достать его из failed_generation
                recovered = self._parse_failed_generation(getattr(e, "failed_generation", None))
                if recovered:
                    synth = []
                    for k, (nm, ar) in enumerate(recovered):
                        synth.append((nm, ar, {
                            "id": f"call_{k}_{nm}", "type": "function",
                            "function": {"name": nm, "arguments": json.dumps(ar, ensure_ascii=False)},
                        }))
                    messages.append({"role": "assistant", "content": "", "tool_calls": [s[2] for s in synth]})
                    for nm, ar, fixed in synth:
                        out = await self._run_tool_step(status_msg, call, nm, ar)
                        messages.append({"role": "tool", "tool_call_id": fixed["id"], "name": nm, "content": str(out)[:out_limit]})
                    continue
                # не удалось — мягкая деградация: обычный ответ без инструментов
                logger.warning(f"Tool-calling failed for {provider}/{model}, falling back to plain chat: {e}")
                try:
                    text_only, usage = await self._dispatch_openai(provider, model, messages, temperature, None)
                except Exception:
                    raise e
                ti += int(usage.get("prompt_tokens") or usage.get("input_tokens") or 0)
                to += int(usage.get("completion_tokens") or usage.get("output_tokens") or 0)
                final_text = str(text_only or "").strip()
                break
            ti += int(usage.get("prompt_tokens") or usage.get("input_tokens") or 0)
            to += int(usage.get("completion_tokens") or usage.get("output_tokens") or 0)
            content = msg_obj.get("content")
            if isinstance(content, list):
                content = "\n".join(str(p.get("text", p)) for p in content)
            tool_calls = msg_obj.get("tool_calls") or []
            # нормализуем и оставляем только валидные вызовы (иначе провайдер отвергнет переотправку)
            normalized = []
            for tc in tool_calls:
                name, args, fixed = self._normalize_tool_call(tc)
                if fixed:
                    normalized.append((name, args, fixed))
            if not normalized:
                final_text = str(content or "").strip()
                break
            messages.append({"role": "assistant", "content": content or "", "tool_calls": [n[2] for n in normalized]})
            for name, args, fixed in normalized:
                out = await self._run_tool_step(status_msg, call, name, args)
                messages.append({
                    "role": "tool", "tool_call_id": fixed["id"],
                    "name": name, "content": str(out)[:out_limit],
                })
        if not final_text:
            final_text = "<i>(агент остановился, достигнут лимит шагов инструментов)</i>"
        return final_text, ti, to

    def _tool_preview(self, name, args):
        args = args or {}
        if name == "read_file":
            p = os.path.basename(str(args.get("path", "")))
            off = args.get("offset_lines", 1)
            lim = args.get("limit_lines", 200)
            return f"read({p}:{off}-{int(off)+int(lim)-1})" if off != 1 or lim != 200 else f"read({p})"
        if name == "search_in_file":
            p = os.path.basename(str(args.get("path", "")))
            q = str(args.get("query", ""))[:20]
            return f"grep({p}, '{q}')"
        if name == "find_files":
            pat = str(args.get("pattern", "*"))
            return f"find('{pat}')"
        if name == "send_file":
            fn = args.get("filename") or os.path.basename(str(args.get("path", ""))) or "file"
            return f"send_file({fn})"
        if name == "upload_file":
            fn = args.get("filename") or os.path.basename(str(args.get("path", ""))) or "file"
            srv = str(args.get("service", "x0"))
            return f"upload({fn} -> {srv})"
        if name == "tg_action":
            act = str(args.get("action", ""))
            return f"tg_act({act})"
        if name == "replace_in_file":
            p = os.path.basename(str(args.get("path", "")))
            return f"replace_in({p})"
        if name == "read_chat_file":
            mid = args.get("message_id") or "reply"
            return f"chat_file({mid})"
        if name == "write_file":
            p = os.path.basename(str(args.get("path", "")))
            return f"write({p})"
        if name == "run_terminal":
            cmd = str(args.get("command", "")).strip()
            return f"sh({cmd[:35]})"
        if name == "web_search":
            q = str(args.get("query", ""))[:30]
            return f"search('{q}')"
        if name == "fetch_url":
            u = str(args.get("url", ""))[:35]
            return f"fetch({u})"
        a = ", ".join(f"{k}={str(v)[:24]}" for k, v in args.items())
        return f"{name}({a})"

    def _format_tool_step_info(self, step: dict):
        name = step.get("name", "")
        args = step.get("args", {}) or {}
        st = step.get("state", "done")
        dur = float(step.get("duration", 0.0) or 0.0)
        dur_s = f"{int(round(dur))}s" if dur >= 0.95 else f"{round(dur, 1)}s"
        
        st_icon = "✓" if st == "done" else "✗" if st == "err" else "◴"
        status_word = "готово" if st == "done" else "ошибка" if st == "err" else "выполняется"
        
        if name == "run_terminal":
            raw_cmd = str(args.get("command", "")).strip()
            lines = [l.strip() for l in raw_cmd.splitlines() if l.strip()]
            cmd = lines[0] if lines else raw_cmd
            if len(lines) > 1:
                cmd += " ..."
            if len(cmd) > 90:
                cmd = cmd[:87] + "..."
            res_disp = f"bash: {cmd}"
            prog_disp = cmd
        elif name == "read_file":
            p = str(args.get("path", "")).strip()
            res_disp = f"read: {p}"
            prog_disp = f"read {p}"
        elif name == "write_file":
            p = str(args.get("path", "")).strip()
            res_disp = f"write: {p}"
            prog_disp = f"write {p}"
        elif name == "web_search":
            q = str(args.get("query", "")).strip()
            res_disp = f"search: {q}"
            prog_disp = f"search {q}"
        elif name == "fetch_url":
            u = str(args.get("url", "")).strip()
            res_disp = f"fetch: {u}"
            prog_disp = f"fetch {u}"
        elif name == "find_files":
            pat = str(args.get("pattern", "*")).strip()
            res_disp = f"find: {pat}"
            prog_disp = f"find {pat}"
        elif name == "search_in_file":
            p = str(args.get("path", "")).strip()
            q = str(args.get("query", "")).strip()
            res_disp = f"grep: {p} '{q}'"
            prog_disp = f"grep {p} '{q}'"
        elif name == "replace_in_file":
            p = str(args.get("path", "")).strip()
            res_disp = f"replace: {p}"
            prog_disp = f"replace in {p}"
        elif name == "list_dir":
            p = str(args.get("path", "")).strip() or "."
            res_disp = f"ls: {p}"
            prog_disp = f"ls {p}"
        elif name == "send_file":
            fn = str(args.get("filename") or args.get("path") or "file")
            res_disp = f"send_file: {fn}"
            prog_disp = f"send_file {fn}"
        elif name == "upload_file":
            fn = str(args.get("filename") or args.get("path") or "file")
            res_disp = f"upload: {fn}"
            prog_disp = f"upload {fn}"
        elif name == "tg_send":
            ch = str(args.get("chat", "")).strip()
            res_disp = f"tg_send: {ch}"
            prog_disp = f"tg_send {ch}"
        elif name == "tg_history":
            ch = str(args.get("chat", "")).strip()
            res_disp = f"tg_history: {ch}"
            prog_disp = f"tg_history {ch}"
        elif name == "tg_action":
            act = str(args.get("action", "")).strip()
            res_disp = f"tg_act: {act}"
            prog_disp = f"tg_act {act}"
        else:
            prev = self._tool_preview(name, args)
            res_disp = prev
            prog_disp = prev
            
        return st_icon, res_disp, prog_disp, status_word, dur_s

    def _build_tool_details_blocks(self, tool_steps: list, total_elapsed: float = 0.0) -> str:
        if not tool_steps:
            return ""
            
        res_lines = []
        progress_lines = []
        
        for s in tool_steps:
            st_icon, res_disp, prog_disp, status_word, dur_s = self._format_tool_step_info(s)
            res_lines.append(f"• <code>{st_icon} {utils.escape_html(res_disp)}</code>")
            progress_lines.append(f"• <code>инструменты · {utils.escape_html(prog_disp)} · {status_word} · {dur_s}</code>")
            
        tot_s = f"{int(round(total_elapsed))}s" if total_elapsed >= 0.95 else f"{round(total_elapsed, 1)}s"
        progress_lines.append(f"• <code>готовит ответ · ответ · готово · {tot_s}</code>")
        
        results_html = f"<details><summary>Результаты инструментов</summary><b>Результаты инструментов:</b><blockquote>{'\n'.join(res_lines)}</blockquote></details>"
        progress_html = f"<details><summary>Ход работы</summary><b>Ход работы:</b><blockquote>{'\n'.join(progress_lines)}</blockquote></details>"
        
        return f"{results_html}\n{progress_html}"

    async def _render_tool_progress(self, status_msg, call):
        if not getattr(self, "_tool_steps", []):
            return
        raw_prov = self._normalize_provider_name(getattr(self, "_active_provider", None) or self.config.get("provider"))
        provider = self._provider_label(raw_prov)
        model = getattr(self, "_active_model", None) or self._resolve_effective_model(raw_prov)
        start_t = getattr(self, "_tool_start_time", 0.0)
        if not start_t:
            start_t = self._tool_start_time = time.time()
        elapsed = round(max(0.0, time.time() - start_t), 1)
        step_num = len(self._tool_steps)
        cur = self._tool_steps[-1]
        
        cur_state = cur.get("state", "run")
        if cur_state == "run":
            phase = "Выполнение инструмента"
            phase_icon = "◴"
        elif cur_state == "err":
            phase = "Ошибка инструмента"
            phase_icon = "✗"
        else:
            phase = "Обработка результата"
            phase_icon = "✓"
            
        cur_preview = self._tool_preview(cur.get("name", ""), cur.get("args", {}))
        
        # CodexCLI style step progress status with sakura emoji and ∅ bullets
        text = (
            f"<blockquote>"
            f"🌸 <b>magent</b> · <code>{utils.escape_html(model)}</code> · <code>{provider}</code>\n"
            f"∅ <b>{phase}</b> · шаг <code>{step_num}</code> · <code>{elapsed}с</code>\n"
            f"∅ <b>Status:</b> <code>{utils.escape_html(cur_preview)}</code>"
            f"</blockquote>"
        )
        text = self._maybe_clean_symbols(text)
        try:
            if call:
                await call.edit(text.replace('<emoji document_id=', '<tg-emoji emoji-id=').replace('</emoji>', '</tg-emoji>'))
            elif status_msg:
                await utils.answer(status_msg, text)
        except Exception:
            pass

    async def _run_tool_step(self, status_msg, call, name, args):
        """Добавляет шаг в живую панель, выполняет инструмент, обновляет статус, возвращает результат."""
        # --- loop guard: блокируем одинаковые повторные вызовы одного инструмента ---
        repeat_key = json.dumps([name, args or {}], sort_keys=True, ensure_ascii=False, default=str)[:300]
        if not isinstance(getattr(self, "_tool_repeat", None), dict):
            self._tool_repeat = {}
        self._tool_repeat[repeat_key] = self._tool_repeat.get(repeat_key, 0) + 1
        if self._tool_repeat[repeat_key] >= 3:
            step = {"name": name, "args": args or {}, "state": "err",
                    "out": "blocked: repeated identical call", "duration": 0.0}
            self._tool_steps.append(step)
            await self._render_tool_progress(status_msg, call)
            return ("ERROR: loop-guard — этот инструмент уже вызывался с такими же аргументами 3+ раза и в этой сессии. "
                    "НЕ повторяй вызов: либо измени подход (другая команда/путь), либо заверши ответ по имеющимся данным.")
        if len(self._tool_repeat) > 500:
            self._tool_repeat = {}
        t0 = time.time()
        step = {"name": name, "args": args or {}, "state": "run", "out": "", "start_time": t0, "duration": 0.0}
        self._tool_steps.append(step)
        await self._render_tool_progress(status_msg, call)
        try:
            logger.info(f"[tools] {self._tool_preview(name, args)}")
            if self.config.get("tools_confirm") and name == "run_terminal":
                logger.warning(f"[tools] RUN: {(args or {}).get('command', '')}")
        except Exception:
            pass
        out = await self._execute_tool(name, args)
        step["duration"] = max(0.1, round(time.time() - t0, 1))
        step["state"] = "err" if str(out).startswith("ERROR") else "done"
        step["out"] = str(out)
        await self._render_tool_progress(status_msg, call)
        return out

    async def _notify_tool(self, status_msg, call, name, args):
        try:
            preview = name + "(" + ", ".join(f"{k}={str(v)[:40]}" for k, v in args.items()) + ")"
            logger.info(f"[tools] {preview}")
            if self.config.get("tools_confirm") and name == "run_terminal":
                logger.warning(f"[tools] RUN: {args.get('command', '')}")
            txt = self.strings["tools_running"].format(utils.escape_html(preview[:160]))
            txt = self._maybe_clean_symbols(txt)
            if call:
                await call.edit(txt.replace('<emoji document_id=', '<tg-emoji emoji-id=').replace('</emoji>', '</tg-emoji>'))
            elif status_msg:
                await utils.answer(status_msg, txt)
        except Exception:
            pass

    async def _execute_tool(self, name, args):
        try:
            if name == "run_terminal":
                return await self._tool_run_terminal(str(args.get("command", "")))
            if name == "read_file":
                return self._tool_read_file(
                    str(args.get("path", "")),
                    offset_lines=args.get("offset_lines", 1),
                    limit_lines=args.get("limit_lines", 200),
                )
            if name == "write_file":
                return self._tool_write_file(str(args.get("path", "")), str(args.get("content", "")))
            if name == "search_in_file":
                return self._tool_search_in_file(
                    str(args.get("path", "")),
                    str(args.get("query", "")),
                    regex=bool(args.get("regex", False)),
                    context_lines=args.get("context_lines", 2),
                )
            if name == "find_files":
                return self._tool_find_files(
                    path=str(args.get("path", "") or "."),
                    pattern=str(args.get("pattern", "*") or "*"),
                    max_results=int(args.get("max_results", 50) or 50),
                    recursive=bool(args.get("recursive", True)),
                )
            if name == "send_file":
                return await self._tool_send_file(
                    path=args.get("path"),
                    content=args.get("content"),
                    filename=args.get("filename"),
                    caption=args.get("caption"),
                    chat=args.get("chat"),
                )
            if name == "replace_in_file":
                return self._tool_replace_in_file(
                    str(args.get("path", "")),
                    str(args.get("old_text", "")),
                    str(args.get("new_text", "")),
                )
            if name == "read_chat_file":
                return await self._tool_read_chat_file(
                    chat=args.get("chat"),
                    message_id=args.get("message_id"),
                )
            if name == "upload_file":
                return await self._tool_upload_file(
                    path=args.get("path"),
                    content=args.get("content"),
                    filename=args.get("filename"),
                    service=args.get("service", "x0"),
                )
            if name == "tg_action":
                return await self._tool_tg_action(
                    action=str(args.get("action", "")),
                    target=args.get("target"),
                    message_ids=args.get("message_ids"),
                    limit=args.get("limit", 20),
                    query=args.get("query"),
                )
            if name == "list_dir":
                return self._tool_list_dir(str(args.get("path", "") or "."))
            if name == "tg_send":
                return await self._tool_tg_send(str(args.get("chat", "")), str(args.get("text", "")))
            if name == "tg_history":
                return await self._tool_tg_history(str(args.get("chat", "")), int(args.get("limit", 20) or 20))
            if name == "web_search":
                return await self._tool_web_search(str(args.get("query", "")))
            if name == "fetch_url":
                return await self._tool_fetch_url(str(args.get("url", "")))
            if name == "save_skill":
                s_name = str(args.get("name", "")).strip() or f"skill_{len(self.skills) + 1}"
                s_content = str(args.get("content", "")).strip()
                if not s_content:
                    return "ERROR: empty content"
                self.skills[s_name] = s_content
                self._save_skills()
                return f"OK: skill '{s_name}' saved permanently ({len(self.skills)} total)"
            return f"ERROR: unknown tool {name}"
        except Exception as e:
            return f"ERROR: {type(e).__name__}: {e}"

    def _tools_cwd(self):
        wd = str(self.config.get("tools_workdir") or "").strip()
        return wd if wd and os.path.isdir(wd) else None

    async def _tool_run_terminal(self, command):
        if not command.strip():
            return "ERROR: empty command"
        timeout = int(self.config["tools_shell_timeout"])
        proc = await asyncio.create_subprocess_shell(
            command,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT,
            cwd=self._tools_cwd(),
        )
        try:
            out, _ = await asyncio.wait_for(proc.communicate(), timeout=timeout)
        except asyncio.TimeoutError:
            try: proc.kill()
            except Exception: pass
            return f"ERROR: timeout after {timeout}s"
        text = (out or b"").decode("utf-8", errors="replace")
        limit = int(self.config["tools_output_limit"])
        if len(text) > limit:
            text = text[:limit] + f"\n...[truncated {len(text) - limit} chars]"
        return f"exit_code={proc.returncode}\n{text or '(no output)'}"

    def _tool_read_file(self, path, offset_lines=1, limit_lines=200):
        if not path:
            return "ERROR: empty path"
        p = os.path.expanduser(path)
        if not os.path.isfile(p):
            return f"ERROR: not a file: {path}"
        try:
            size = os.path.getsize(p)
            encodings = ("utf-8", "cp1251", "latin-1")
            lines = None
            for enc in encodings:
                try:
                    with open(p, "r", encoding=enc) as f:
                        lines = f.readlines()
                    break
                except UnicodeDecodeError:
                    continue
            if lines is None:
                return f"ERROR: cannot decode file {path}"
            
            total = len(lines)
            start_idx = max(1, int(offset_lines or 1)) - 1
            cnt = max(1, min(int(limit_lines or 200), 1000))
            end_idx = min(start_idx + cnt, total)
            
            selected = lines[start_idx:end_idx]
            out_lines = [f"{i}: {line.rstrip(chr(13) + chr(10))}" for i, line in enumerate(selected, start=start_idx + 1)]
            header = f"[{p} | Lines {start_idx + 1}-{end_idx} of {total} | {size} bytes]:"
            return header + "\n" + "\n".join(out_lines)
        except Exception as e:
            return f"ERROR reading file {path}: {e}"

    def _tool_write_file(self, path, content):
        if not path:
            return "ERROR: empty path"
        p = os.path.expanduser(path)
        d = os.path.dirname(p)
        if d and not os.path.isdir(d):
            os.makedirs(d, exist_ok=True)
        with open(p, "w", encoding="utf-8") as f:
            f.write(content)
        return f"OK: written {len(content)} chars to {p}"

    def _tool_search_in_file(self, path, query, regex=False, context_lines=2):
        if not path or not query:
            return "ERROR: path and query required"
        p = os.path.expanduser(path)
        if not os.path.isfile(p):
            return f"ERROR: not a file: {path}"
        try:
            encodings = ("utf-8", "cp1251", "latin-1")
            lines = None
            for enc in encodings:
                try:
                    with open(p, "r", encoding=enc) as f:
                        lines = f.readlines()
                    break
                except UnicodeDecodeError:
                    continue
            if lines is None:
                return f"ERROR: cannot decode {path}"
            
            c_lines = max(0, min(int(context_lines or 2), 10))
            is_regex = bool(regex)
            pattern = re.compile(query, re.IGNORECASE) if is_regex else None
            
            matching_indices = set()
            for idx, line in enumerate(lines):
                matched = bool(pattern.search(line)) if pattern else (query.lower() in line.lower())
                if matched:
                    matching_indices.add(idx)
            
            if not matching_indices:
                return f"No matches found for '{query}' in {path} ({len(lines)} lines scanned)."
            
            sorted_indices = sorted(matching_indices)
            display_blocks = []
            rendered_lines = set()
            for m_idx in sorted_indices[:50]:
                block_start = max(0, m_idx - c_lines)
                block_end = min(len(lines), m_idx + c_lines + 1)
                block_lines = []
                for l_i in range(block_start, block_end):
                    if l_i in rendered_lines:
                        continue
                    rendered_lines.add(l_i)
                    prefix = ">> " if l_i in matching_indices else "   "
                    block_lines.append(f"{prefix}{l_i + 1}: {lines[l_i].rstrip(chr(13) + chr(10))}")
                if block_lines:
                    display_blocks.append("\n".join(block_lines))
            
            return f"Found {len(matching_indices)} match(es) for '{query}' in {path}:\n" + "\n---\n".join(display_blocks)
        except Exception as e:
            return f"ERROR searching in {path}: {e}"

    def _tool_find_files(self, path=".", pattern="*", max_results=50, recursive=True):
        import fnmatch
        base_dir = os.path.expanduser(path or ".")
        if not os.path.isdir(base_dir):
            return f"ERROR: not a directory: {path}"
        results = []
        limit = max(1, min(int(max_results or 50), 200))
        pat = pattern or "*"
        
        if not recursive:
            try:
                for entry in sorted(os.listdir(base_dir)):
                    if fnmatch.fnmatch(entry, pat):
                        full = os.path.join(base_dir, entry)
                        size = os.path.getsize(full) if os.path.isfile(full) else 0
                        results.append(f"{'[file]' if os.path.isfile(full) else '[dir] '} {entry} ({size} B)")
                        if len(results) >= limit:
                            break
            except Exception as e:
                return f"ERROR: {e}"
        else:
            for root, dirs, files in os.walk(base_dir):
                for f in files:
                    if fnmatch.fnmatch(f, pat):
                        full = os.path.join(root, f)
                        try:
                            size = os.path.getsize(full)
                            rel = os.path.relpath(full, base_dir)
                            results.append(f"[file] {rel} ({size} B)")
                        except Exception:
                            pass
                        if len(results) >= limit:
                            break
                if len(results) >= limit:
                    break
        
        if not results:
            return f"No files matching '{pat}' found in {base_dir}."
        return f"Files matching '{pat}' in {base_dir} ({len(results)} found):\n" + "\n".join(results)

    async def _tool_send_file(self, path=None, content=None, filename=None, caption=None, chat=None):
        target_chat = chat or self._current_tool_chat_id or "me"
        entity = await self._tool_resolve_entity(target_chat)
        caption_text = caption or ""
        
        if path:
            p = os.path.expanduser(str(path).strip())
            if not os.path.isfile(p):
                return f"ERROR: file does not exist: {path}"
            try:
                msg = await self.client.send_file(entity, p, caption=caption_text)
                return f"OK: file '{os.path.basename(p)}' sent successfully to {target_chat} (msg_id={getattr(msg, 'id', None)})"
            except Exception as e:
                return f"ERROR sending file {path} to {target_chat}: {e}"
        
        if content is not None:
            fname = filename or "file.txt"
            raw_bytes = content.encode("utf-8") if isinstance(content, str) else bytes(content)
            buf = io.BytesIO(raw_bytes)
            buf.name = fname
            try:
                msg = await self.client.send_file(entity, buf, caption=caption_text)
                return f"OK: generated file '{fname}' ({len(raw_bytes)} bytes) sent successfully to {target_chat} (msg_id={getattr(msg, 'id', None)})"
            except Exception as e:
                return f"ERROR sending generated file {fname} to {target_chat}: {e}"
        
        return "ERROR: either 'path' (file on disk) or 'content' (with optional 'filename') must be provided"

    def _tool_replace_in_file(self, path, old_text, new_text):
        if not path or old_text is None or new_text is None:
            return "ERROR: path, old_text, and new_text required"
        p = os.path.expanduser(str(path).strip())
        if not os.path.isfile(p):
            return f"ERROR: not a file: {path}"
        try:
            with open(p, "r", encoding="utf-8") as f:
                content = f.read()
            if old_text not in content:
                return f"ERROR: old_text not found in {path}. Make sure text matches exactly."
            count = content.count(old_text)
            new_content = content.replace(old_text, new_text)
            with open(p, "w", encoding="utf-8") as f:
                f.write(new_content)
            return f"OK: replaced {count} occurrence(s) in {path}."
        except Exception as e:
            return f"ERROR replacing text in {path}: {e}"

    async def _tool_read_chat_file(self, chat=None, message_id=None):
        target_chat = chat or self._current_tool_chat_id or "me"
        entity = await self._tool_resolve_entity(target_chat)
        target_msg = None
        if message_id:
            try:
                target_msg = await self.client.get_messages(entity, ids=int(message_id))
            except Exception as e:
                return f"ERROR fetching message {message_id}: {e}"
        elif getattr(self, "_current_tool_message", None):
            try:
                target_msg = await self._current_tool_message.get_reply_message()
            except Exception:
                pass
        
        if not target_msg:
            return "ERROR: no message with file found. Specify message_id or reply to a message containing a file."
        
        if not (target_msg.document or target_msg.photo or target_msg.audio or target_msg.video):
            if target_msg.text:
                return f"[Message text]:\n{target_msg.text[:2000]}"
            return "ERROR: target message has no media or file attached."
        
        try:
            raw_bytes = await target_msg.download_media(bytes)
            if not raw_bytes:
                return "ERROR: failed to download media."
            if len(raw_bytes) > 20 * 1024 * 1024:
                return f"ERROR: file too large ({len(raw_bytes)} bytes > 20MB limit)"
            for enc in ("utf-8", "cp1251", "latin-1"):
                try:
                    text_content = raw_bytes.decode(enc)
                    return f"[File from chat ({len(raw_bytes)} bytes)]:\n{text_content[:4000]}"
                except UnicodeDecodeError:
                    continue
            return f"Binary file downloaded successfully ({len(raw_bytes)} bytes), filename: {getattr(target_msg.file, 'name', 'unknown')}"
        except Exception as e:
            return f"ERROR reading chat file: {e}"

    async def _tool_upload_file(self, path=None, content=None, filename=None, service="x0"):
        srv = str(service or "x0").strip().lower()
        file_bytes = None
        fname = filename or "file.txt"
        if path:
            p = os.path.expanduser(str(path).strip())
            if not os.path.isfile(p):
                return f"ERROR: file not found: {path}"
            fname = filename or os.path.basename(p)
            with open(p, "rb") as f:
                file_bytes = f.read()
        elif content is not None:
            file_bytes = content.encode("utf-8") if isinstance(content, str) else bytes(content)
            fname = filename or "upload.txt"
        else:
            return "ERROR: either path or content required"
            
        try:
            session = self._tools_aiohttp_session()
            async with session:
                data = aiohttp.FormData()
                if srv in ("0x0", "0x0.st"):
                    url = "https://0x0.st"
                    data.add_field("file", file_bytes, filename=fname)
                elif srv in ("catbox", "catbox.moe"):
                    url = "https://catbox.moe/user/api.php"
                    data.add_field("reqtype", "fileupload")
                    data.add_field("fileToUpload", file_bytes, filename=fname)
                else:
                    url = "https://x0.at"
                    data.add_field("file", file_bytes, filename=fname)
                    
                async with session.post(url, data=data, timeout=30) as resp:
                    resp_text = (await resp.text()).strip()
                    if resp.status == 200 and resp_text.startswith("http"):
                        return f"OK: uploaded to {resp_text}"
                    return f"ERROR: upload status {resp.status}: {resp_text[:200]}"
        except Exception as e:
            return f"ERROR uploading file: {e}"

    async def _tool_tg_action(self, action, target=None, message_ids=None, limit=20, query=None):
        act = (action or "").strip().lower()
        target_chat = target or self._current_tool_chat_id or "me"
        entity = await self._tool_resolve_entity(target_chat)
        
        if act == "pin_message":
            mid = int(message_ids[0] if isinstance(message_ids, list) and message_ids else (message_ids or 0))
            if not mid:
                return "ERROR: message_ids required for pin_message"
            await self.client.pin_message(entity, mid, notify=False)
            return f"OK: pinned message {mid} in {target_chat}"
            
        if act == "unpin_message":
            mid = int(message_ids[0] if isinstance(message_ids, list) and message_ids else (message_ids or 0))
            await self.client.unpin_message(entity, mid if mid else None)
            return f"OK: unpinned message {mid or 'all'} in {target_chat}"
            
        if act == "delete_messages":
            mids = [int(m) for m in message_ids] if isinstance(message_ids, list) else ([int(message_ids)] if message_ids else [])
            if not mids:
                n = max(1, min(int(limit or 1), 100))
                mids = []
                async for m in self.client.iter_messages(entity, limit=n):
                    mids.append(m.id)
            if not mids:
                return "ERROR: no messages to delete"
            await self.client.delete_messages(entity, mids, revoke=True)
            return f"OK: deleted {len(mids)} message(s) from {target_chat}"
            
        if act == "get_chat_info":
            info = {
                "id": getattr(entity, "id", None),
                "title": getattr(entity, "title", None) or get_display_name(entity),
                "username": getattr(entity, "username", None),
                "megagroup": bool(getattr(entity, "megagroup", False)),
                "broadcast": bool(getattr(entity, "broadcast", False)),
            }
            return json.dumps(info, ensure_ascii=False)
            
        if act == "get_user_info":
            user_ent = await self._tool_resolve_entity(target if target else "me")
            info = {
                "id": getattr(user_ent, "id", None),
                "first_name": getattr(user_ent, "first_name", None),
                "last_name": getattr(user_ent, "last_name", None),
                "username": getattr(user_ent, "username", None),
                "bot": bool(getattr(user_ent, "bot", False)),
                "phone": getattr(user_ent, "phone", None),
            }
            return json.dumps(info, ensure_ascii=False)
            
        if act == "search_messages":
            q = str(query or "").strip()
            n = max(1, min(int(limit or 15), 50))
            results = []
            async for m in self.client.iter_messages(entity, search=q, limit=n):
                who = getattr(m.sender, "first_name", "") or str(m.sender_id)
                results.append(f"[{m.id}] {who}: {(m.text or '')[:120]}")
            return f"Search for '{q}' in {target_chat} ({len(results)} found):\n" + "\n".join(results)
            
        if act == "get_dialogs":
            n = max(1, min(int(limit or 15), 50))
            dialogs = []
            async for d in self.client.iter_dialogs(limit=n):
                dialogs.append(f"[{d.id}] {d.name} ({'channel' if d.is_channel else 'group' if d.is_group else 'user'})")
            return f"Recent dialogs ({len(dialogs)}):\n" + "\n".join(dialogs)
            
        if act == "mark_chat_read":
            await self.client.send_read_acknowledge(entity)
            return f"OK: marked {target_chat} as read"
            
        return f"ERROR: unknown action '{action}'. Supported: pin_message, unpin_message, delete_messages, get_chat_info, get_user_info, search_messages, get_dialogs, mark_chat_read."

    def _tool_list_dir(self, path):
        p = os.path.expanduser(path or ".")
        if not os.path.isdir(p):
            return f"ERROR: not a dir: {path}"
        items = []
        for name in sorted(os.listdir(p))[:300]:
            full = os.path.join(p, name)
            items.append(("[dir]  " if os.path.isdir(full) else "[file] ") + name)
        return f"{p}:\n" + "\n".join(items) if items else f"{p}: (empty)"

    async def _tool_resolve_entity(self, chat):
        chat = str(chat).strip()
        if chat.lower() in ("me", "self", "saved", "избранное"):
            return "me"
        if re.fullmatch(r"-?\d+", chat):
            return int(chat)
        return chat

    async def _tool_tg_send(self, chat, text):
        if not text.strip():
            return "ERROR: empty text"
        entity = await self._tool_resolve_entity(chat)
        msg = await self.client.send_message(entity, text)
        return f"OK: sent message id={getattr(msg, 'id', None)} to {chat}"

    async def _tool_tg_history(self, chat, limit):
        entity = await self._tool_resolve_entity(chat)
        limit = max(1, min(int(limit or 20), 50))
        lines = []
        async for m in self.client.iter_messages(entity, limit=limit):
            try:
                who = get_display_name(await m.get_sender()) if m.sender_id else "?"
            except Exception:
                who = str(m.sender_id)
            body = (m.text or getattr(m, "message", "") or "").replace("\n", " ")
            lines.append(f"[{m.id}] {who}: {body[:200]}")
        return "\n".join(reversed(lines)) or "(no messages)"

    def _html_to_text(self, html_src: str) -> str:
        from html import unescape
        h = html_src or ""
        h = re.sub(r"(?is)<(script|style|noscript|template|svg)[^>]*>.*?</\1>", " ", h)
        h = re.sub(r"(?is)<br\s*/?>", "\n", h)
        h = re.sub(r"(?is)</(p|div|li|h[1-6]|tr|table|ul|ol|section|article|header|footer)>", "\n", h)
        h = re.sub(r"(?s)<[^>]+>", " ", h)
        h = unescape(h)
        h = re.sub(r"[ \t\f\r]+", " ", h)
        h = re.sub(r"\n\s*\n\s*\n+", "\n\n", h)
        return h.strip()

    def _tools_aiohttp_session(self):
        proxy = self.config.get("proxy") or None
        connector = None
        req_proxy = proxy
        if proxy and proxy.startswith(("socks4://", "socks5://", "http://", "https://")):
            try:
                from aiohttp_socks import ProxyConnector
                connector = ProxyConnector.from_url(proxy)
                req_proxy = None
            except Exception:
                req_proxy = proxy
        return aiohttp.ClientSession(connector=connector), req_proxy

    def _tool_user_agent(self):
        return ("Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")

    async def _tool_fetch_url(self, url):
        url = str(url).strip()
        if not url:
            return "ERROR: empty url"
        if not re.match(r"(?i)^https?://", url):
            url = "https://" + url
        headers = {"User-Agent": self._tool_user_agent(), "Accept-Language": "ru,en;q=0.8"}
        session, req_proxy = self._tools_aiohttp_session()
        try:
            async with session as s:
                async with s.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=30), allow_redirects=True) as r:
                    status = r.status
                    ctype = r.headers.get("Content-Type", "")
                    raw = await r.text(errors="replace")
        except Exception as e:
            return f"ERROR: fetch failed: {type(e).__name__}: {str(e)[:120]}"
        body = raw if ("text/html" not in ctype and "<html" not in raw[:2000].lower()) else self._html_to_text(raw)
        limit = int(self.config["tools_output_limit"])
        truncated = "\n...[truncated]" if len(body) > limit else ""
        return f"URL: {url}\nHTTP {status} · {ctype or '?'}\n\n{body[:limit]}{truncated}"

    async def _tool_web_search(self, query):
        q = str(query).strip()
        if not q:
            return "ERROR: empty query"
        import urllib.parse as _up
        headers = {"User-Agent": self._tool_user_agent(), "Accept-Language": "ru,en;q=0.8"}
        session, req_proxy = self._tools_aiohttp_session()
        try:
            async with session as s:
                async with s.post("https://html.duckduckgo.com/html/", data={"q": q},
                                  headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=25)) as r:
                    html_src = await r.text(errors="replace")
        except Exception as e:
            return f"ERROR: search failed: {type(e).__name__}: {str(e)[:120]}"
        results = []
        anchors = re.findall(r'class="result__a"[^>]*href="([^"]+)"[^>]*>(.*?)</a>', html_src, re.S)
        snippets = re.findall(r'class="result__snippet"[^>]*>(.*?)</a>', html_src, re.S)
        for idx, (href, title_html) in enumerate(anchors[:6]):
            if "uddg=" in href:
                m = re.search(r"uddg=([^&]+)", href)
                if m:
                    href = _up.unquote(m.group(1))
            title = self._html_to_text(title_html)
            snip = self._html_to_text(snippets[idx]) if idx < len(snippets) else ""
            line = f"{idx + 1}. {title}\n   {href}"
            if snip:
                line += f"\n   {snip[:200]}"
            results.append(line)
        if not results:
            return "No results (или DuckDuckGo сменил разметку). Попробуй fetch_url с конкретным сайтом."
        return f"Результаты поиска «{q}»:\n\n" + "\n\n".join(results)

    async def _format_final_response(self, chat_id, base_message_id, request_text, result_text, provider, model, elapsed, tokens_in, tokens_out, history_key, call, status_msg, attempt):
        hist_len = len(self._get_structured_history(history_key)) // 2
        max_hist = self.config["max_history_length"]
        is_global = history_key == "global_context"
        
        if is_global:
            mem_indicator = self.strings["memory_status_global"].format(hist_len)
        elif max_hist <= 0:
            mem_indicator = self.strings["memory_status_unlimited"].format(hist_len)
        else:
            mem_indicator = self.strings["memory_status"].format(hist_len, max_hist)
        
        model_info = self._model_info_line(provider, model, elapsed, tokens_in, tokens_out)
        if attempt > 1:
            model_info += f" <i>(Успешно с {attempt}-й попытки)</i>"
        
        is_long_text = len(result_text) > 3500
        if is_long_text and self.config["inline_pagination"]:
            chunks = self._paginate_text(result_text, 3000)
            uid = uuid.uuid4().hex[:6]
            header = f"{mem_indicator}\n{model_info}\n{self.strings['question_prefix']} <blockquote>{utils.escape_html(request_text[:100])}...</blockquote>\n\n{self.strings['response_prefix']}\n"
            self.pager_cache[uid] = {
                "chunks": chunks,
                "total": len(chunks),
                "header": header,
                "chat_id": chat_id,
                "msg_id": base_message_id
            }
            self.db.set(self.strings["name"], DB_PAGER_CACHE_KEY, self.pager_cache)
            await self._render_page(uid, 0, call or status_msg)
        elif len(result_text) > 4096:
            file = io.BytesIO(f"Q: {request_text}\nA:\n{result_text}".encode("utf-8"))
            file.name = "response.txt"
            if call:
                await call.answer("File...", show_alert=False)
                await self.client.send_file(call.chat_id, file, caption=self.strings["response_too_long"], reply_to=call.message_id)
            elif status_msg:
                await status_msg.delete()
                await self.client.send_file(chat_id, file, caption=self.strings["response_too_long"], reply_to=base_message_id)
        else:
            thinking_parts = []
            def _extract_think(m):
                thinking_parts.append(m.group(1).strip())
                return ""
            clean_result = re.sub(r"<(?:think|thought)>(.*?)</(?:think|thought)>", _extract_think, result_text, flags=re.DOTALL).strip()
            thinking_text = "\n\n".join(thinking_parts).strip()
            
            response_html = self._markdown_to_html(clean_result or result_text)
            formatted_body = self._format_response_with_smart_separation(response_html)
            thinking_block = f"<blockquote expandable='true'><i>⌬ Ход мыслей:</i>\n{utils.escape_html(thinking_text)}</blockquote>\n\n" if thinking_text else ""
            
            tool_summary = ""
            if getattr(self, "_tool_steps", []):
                tool_summary = self._build_tool_details_blocks(self._tool_steps, elapsed) + "\n\n"
            
            question_html = f"<blockquote expandable='true'>{utils.escape_html(request_text[:180])}</blockquote>"
            text_to_send = (
                f"{mem_indicator}\n{model_info}\n\n"
                f"{self.strings['question_prefix']}\n{question_html}\n\n"
                f"{self.strings['response_prefix']}\n{formatted_body}\n\n"
                f"{tool_summary}{thinking_block}"
            ).strip()
            if call or self.config["interactive_buttons"]:
                text_to_send = text_to_send.replace('<emoji document_id=', '<tg-emoji emoji-id=').replace('</emoji>', '</tg-emoji>')
            text_to_send = self._maybe_clean_symbols(text_to_send)
            buttons = self._get_inline_buttons(chat_id, base_message_id) if self.config["interactive_buttons"] else None
            
            # Telegram Rich Mode
            if self.config.get("rich_mode", True) and not call and status_msg:
                try:
                    rich_html = self._build_rich_response(
                        request_text, result_text, provider, model, elapsed,
                        tokens_in, tokens_out, mem_indicator, getattr(self, "_tool_steps", [])
                    )
                    rich_html = self._maybe_clean_symbols(rich_html)
                    sent = await utils.answer_with_media_fallback(
                        status_msg, text_to_send, rich_message=rich_html, reply_markup=buttons
                    )
                    if sent:
                        return ""
                except Exception as e:
                    logger.warning(f"Rich mode send failed, falling back to standard: {e}")
            
            if call:
                await call.edit(text_to_send, reply_markup=buttons)
                await self._refresh_premium_emoji(call, text_to_send, buttons, is_call=True)
            elif status_msg:
                sent = await utils.answer(status_msg, text_to_send, reply_markup=buttons)
                await self._refresh_premium_emoji(sent or status_msg, text_to_send, buttons, is_call=False)
        return ""

    def _markdown_to_rich_html(self, text: str) -> str:
        code_blocks = []
        def save_code(m):
            lang = m.group(1).strip()
            code = m.group(2).strip()
            idx = len(code_blocks)
            code_blocks.append((lang, code))
            return f"___CODE_BLOCK_{idx}___"
        
        t = re.sub(r"```(.*?)\n([\s\S]+?)\n```", save_code, text)
        t = re.sub(r"^###\s+(.*)", r"<h4>\1</h4>", t, flags=re.M)
        t = re.sub(r"^##\s+(.*)", r"<h3>\1</h3>", t, flags=re.M)
        t = re.sub(r"^#\s+(.*)", r"<h2>\1</h2>", t, flags=re.M)
        t = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", t)
        t = re.sub(r"\*(.+?)\*", r"<i>\1</i>", t)
        t = re.sub(r"`([^`\n]+)`", lambda m: f"<code>{utils.escape_html(m.group(1))}</code>", t)
        
        paragraphs = []
        for block in re.split(r"\n\s*\n", t):
            block = block.strip()
            if not block:
                continue
            if block.startswith("___CODE_BLOCK_"):
                m = re.match(r"___CODE_BLOCK_(\d+)___", block)
                if m:
                    lang, code = code_blocks[int(m.group(1))]
                    cls_attr = f' class="language-{utils.escape_html(lang)}"' if lang else ""
                    paragraphs.append(f'<pre><code{cls_attr}>{utils.escape_html(code)}</code></pre>')
                    continue
            if block.startswith("<h") and block.endswith(">"):
                paragraphs.append(block)
            elif block.startswith("<blockquote>") or block.startswith("<details>"):
                paragraphs.append(block)
            else:
                lines = [l.strip() for l in block.splitlines() if l.strip()]
                if all(l.startswith(("- ", "* ", "• ")) for l in lines):
                    items = "".join(f"<li>{l[2:]}</li>" for l in lines)
                    paragraphs.append(f"<ul>{items}</ul>")
                else:
                    paragraphs.append(f"<p>{'<br>'.join(lines)}</p>")
        return "\n".join(paragraphs)

    def _build_rich_response(self, request_text, result_text, provider, model, elapsed, tokens_in, tokens_out, mem_indicator, tool_steps):
        thinking_parts = []
        def _extract_think(m):
            thinking_parts.append(m.group(1).strip())
            return ""
        clean_text = re.sub(r"<(?:think|thought)>(.*?)</(?:think|thought)>", _extract_think, result_text, flags=re.DOTALL).strip()
        thinking_text = "\n\n".join(thinking_parts).strip()
        
        body_html = self._markdown_to_rich_html(clean_text)
        
        tools_html = ""
        if tool_steps:
            tools_html = self._build_tool_details_blocks(tool_steps, elapsed) + "\n"
            
        thinking_html = ""
        if thinking_text:
            thinking_html = f"<details><summary>⌬ Ход мыслей модели ({len(thinking_text)} симв.)</summary><tg-thinking>{utils.escape_html(thinking_text)}</tg-thinking></details>"
            
        short_req = utils.escape_html(request_text[:60]) + ("..." if len(request_text) > 60 else "")
        req_details = f"<details><summary>» Запрос: {short_req}</summary><p>{utils.escape_html(request_text)}</p></details>"
        
        tok_str = f" · ◈ {tokens_in}↑ {tokens_out}↓" if self.config["show_tokens"] and (tokens_in or tokens_out) else ""
        time_str = f" · ◴ {elapsed}s" if self.config["show_time"] else ""
        header = f"<h3>✦ {self._provider_label(provider)} · <code>{model}</code></h3><p>{mem_indicator}{time_str}{tok_str}</p>"
        
        divider = "<hr>" if (tools_html or thinking_html) else ""
        return f"{header}{req_details}{body_html}{divider}{tools_html}{thinking_html}"

    async def _refresh_premium_emoji(self, target, text, buttons, is_call=False):
        """Доп. перерисовка сообщения — Telegram подхватывает премиум-эмодзи."""
        if not self.config.get("premium_emoji_refresh", True):
            return
        me = getattr(self, "me", None)
        if not getattr(me, "premium", False):
            return
        if self.config.get("clean_symbols_mode", True):
            return
        if self.config.get("rich_mode", True) or "<details" in text or "<tg-thinking" in text:
            return
        try:
            await asyncio.sleep(0.12)
            refreshed = text + "⁠"  # word-joiner
            if is_call:
                await target.edit(refreshed, reply_markup=buttons)
            else:
                await utils.answer(target, refreshed, reply_markup=buttons)
        except Exception:
            pass

    async def _handle_api_error(self, error, impersonation_mode, call, status_msg, chat_id, base_message_id, regeneration, attempt):
        error_text = self._handle_error(error)
        error_buttons = None
        if not impersonation_mode and base_message_id:
            btn_action = "regen_att" if regeneration else "retry"
            is_regen_flag = "1" if regeneration else "0"
            error_buttons = [[
                {"text": f"↺ Повторить ({attempt + 1})", "data": f"gemini:{btn_action}:{chat_id}:{base_message_id}:{attempt + 1}"},
                {"text": "» Запрос", "data": f"gemini:shreq:{is_regen_flag}:{chat_id}:{base_message_id}:{attempt + 1}"}
            ]]
        if impersonation_mode:
            logger.error(f"Gauto error: {error_text}")
        elif call:
            await call.edit(error_text, reply_markup=error_buttons)
        elif status_msg:
            await utils.answer(status_msg, error_text, reply_markup=error_buttons)
        return None
    # =========================================================================
    # Вспомогательные методы для API
    # =========================================================================

    def _process_parts_for_openai(self, parts, default_text):
        content_list = []
        media_notes = []
        for p in parts:
            if hasattr(p, "text") and p.text:
                content_list.append({"type": "text", "text": p.text})
            elif hasattr(p, "inline_data") and p.inline_data:
                mime = p.inline_data.mime_type
                data = p.inline_data.data
                if mime.startswith("image/"):
                    b64_img = base64.b64encode(data).decode("utf-8")
                    content_list.append({"type": "image_url", "image_url": {"url": f"data:{mime};base64,{b64_img}"}})
                elif mime.startswith("audio/"):
                    media_notes.append("[аудиофайл]")
                elif mime.startswith("video/"):
                    media_notes.append("[видеофайл]")
                else:
                    media_notes.append("[файл]")
        
        if media_notes:
            note = "Контекст медиа: " + ", ".join(media_notes)
            if content_list and content_list[0].get("type") == "text":
                content_list[0]["text"] = note + "\n\n" + content_list[0]["text"]
            else:
                content_list.insert(0, {"type": "text", "text": note})
        
        if not content_list:
            return default_text
        return content_list

    def _prepare_google_contents(self, history_key, impersonation_mode, regeneration):
        raw_hist = self._get_structured_history(history_key, gauto=impersonation_mode)
        if regeneration and raw_hist:
            raw_hist = raw_hist[:-2]
        
        contents = []
        try: 
            user_tz = pytz.timezone(self.config["timezone"])
        except pytz.UnknownTimeZoneError: 
            user_tz = pytz.utc
        
        for item in raw_hist:
            content_text = item.get('content', '')
            if 'date' in item and item['date']:
                dt = datetime.fromtimestamp(item['date'], user_tz)
                content_text = f"[{dt.strftime('%d.%m.%Y %H:%M')}] {content_text}"
            contents.append(types.Content(role=item['role'], parts=[types.Part(text=content_text)]))
        return contents

    def _convert_google_history_to_openai(self, history: list, system_prompt: str) -> list:
        messages = []
        if system_prompt:
            messages.append({"role": "system", "content": system_prompt})
        try:
            user_tz = pytz.timezone(self.config["timezone"])
        except:
            user_tz = pytz.utc
        for item in history:
            role = "assistant" if item['role'] == "model" else "user"
            content = item.get("content", "")
            if 'date' in item and item['date']:
                dt = datetime.fromtimestamp(item['date'], user_tz)
                content = f"[{dt.strftime('%d.%m.%Y %H:%M')}] {content}"
            messages.append({"role": role, "content": content})
        return messages

    # =========================================================================
    # Провайдер-специфичные методы API
    # =========================================================================

    async def _send_to_openrouter_api(self, model, messages, temperature, tools=None):
        keys = self._get_openrouter_keys()
        if not keys:
            raise ValueError(self.strings["no_api_key_openrouter"])
        return await self._send_openai_compatible(
            keys, "https://openrouter.ai/api/v1/chat/completions",
            model, messages, temperature, "openrouter",
            extra_headers={"HTTP-Referer": "https://github.com/kgpix", "X-Title": "Gemini Module"},
            tools=tools
        )

    async def _send_to_openai_api(self, model, messages, temperature, tools=None):
        keys = self._get_openai_keys()
        if not keys:
            raise ValueError(self.strings["no_api_key_openai"])
        return await self._send_openai_compatible(
            keys, "https://api.openai.com/v1/chat/completions",
            model, messages, temperature, "openai", tools=tools
        )

    async def _send_to_deepseek_api(self, model, messages, temperature, tools=None):
        keys = self._get_deepseek_keys()
        if not keys:
            raise ValueError(self.strings["no_api_key_deepseek"])
        return await self._send_openai_compatible(
            keys, "https://api.deepseek.com/v1/chat/completions",
            model, messages, temperature, "deepseek", tools=tools
        )

    async def _send_to_huggingface_api(self, model, messages, temperature, tools=None):
        keys = self._get_huggingface_keys()
        if not keys:
            raise ValueError(self.strings["no_api_key_huggingface"])
        # Пробуем новый Inference Providers endpoint (router.huggingface.co)
        try:
            return await self._send_openai_compatible(
                keys, "https://router.huggingface.co/v1/chat/completions",
                model, messages, temperature, "huggingface",
                extra_headers={"X-Provider": "hf-inference"}, tools=tools
            )
        except Exception as hf_err:
            logger.warning(f"HF router endpoint failed: {hf_err}, trying legacy API...")
            # Fallback на старый endpoint
            return await self._send_openai_compatible(
                keys, f"https://api-inference.huggingface.co/models/{model}/v1/chat/completions",
                model, messages, temperature, "huggingface", tools=tools
            )

    def _keys_for(self, provider: str) -> list:
        provider = self._normalize_provider_name(provider)
        if provider == "google":
            if self.api_keys:
                return list(self.api_keys)
            raw = str(self.config.get("api_key") or "")
            return [k.strip() for k in raw.split(",") if k.strip()]
        if provider == "openrouter":
            return self._get_openrouter_keys()
        if provider == "huggingface":
            return self._get_huggingface_keys()
        if provider == "openai":
            return self._get_openai_keys()
        if provider == "deepseek":
            return self._get_deepseek_keys()
        cfg_name = "custom_api_key" if provider == "custom" else f"{provider}_api_key"
        raw = str(self.config.get(cfg_name) or "")
        return [k.strip() for k in raw.split(",") if k.strip()]

    def _resolve_provider_api_key(self, provider: str) -> str:
        provider = self._normalize_provider_name(provider)
        keys = self._keys_for(provider)
        if keys and keys[0] != "dummy":
            return keys[0]
        if provider == "custom":
            return str(self.config.get("custom_api_key") or "")
        return ""

    @property
    def commands(self) -> dict:
        """Справочник команд для .help (только каноничные .m... команды)."""
        raw = getattr(self, "heroku_commands", None)
        if not raw:
            try:
                from ..types import get_commands
                raw = get_commands(self)
            except Exception:
                raw = {}
        return {
            name: func
            for name, func in (raw or {}).items()
            if not (name.startswith("g") or name in ("msymbols", "keytest", "kprov", "kproxytest"))
        }

    def _custom_endpoint(self) -> str:
        base = str(self.config.get("custom_base_url") or "").strip().rstrip("/")
        if not base:
            return ""
        if base.endswith("/chat/completions"):
            return base
        if base.endswith("/v1"):
            return base + "/chat/completions"
        return base + "/v1/chat/completions"

    def _custom_models_endpoint(self) -> str:
        base = str(self.config.get("custom_base_url") or "").strip().rstrip("/")
        if not base:
            return ""
        if base.endswith("/chat/completions"):
            return base.replace("/chat/completions", "/models")
        if base.endswith("/v1"):
            return base + "/models"
        if base.endswith("/models"):
            return base
        return base + "/v1/models"

    async def _send_to_generic_openai(self, provider, model, messages, temperature, tools=None):
        provider = self._normalize_provider_name(provider)
        keys = self._keys_for(provider)
        if provider == "custom":
            url = self._custom_endpoint()
            if not url:
                raise ValueError("▲ <b>Не задан custom_base_url.</b>\nУкажите URL сервера в конфиге: <code>.cfg magent custom_base_url http://...</code> или переключите провайдера через <code>.mprovider</code>")
            if not keys:
                keys = ["dummy"]
        else:
            url = self.OPENAI_COMPAT_ENDPOINTS.get(provider)
            if not url:
                raise ValueError(f"Unknown provider: {provider}")
            if not keys:
                cfg_name = f"{provider}_api_key"
                raise ValueError(f"▲ <b>API ключ для {self._provider_label(provider)} не настроен.</b>\n<code>.cfg magent {cfg_name}</code>")
        return await self._send_openai_compatible(keys, url, model, messages, temperature, provider, tools=tools)

    async def _dispatch_openai(self, provider, model, messages, temperature, tools=None):
        if provider == "openrouter":
            return await self._send_to_openrouter_api(model, messages, temperature, tools)
        if provider == "openai":
            return await self._send_to_openai_api(model, messages, temperature, tools)
        if provider == "deepseek":
            return await self._send_to_deepseek_api(model, messages, temperature, tools)
        if provider == "huggingface":
            return await self._send_to_huggingface_api(model, messages, temperature, tools)
        return await self._send_to_generic_openai(provider, model, messages, temperature, tools)

    async def _send_openai_compatible(self, keys, url, model, messages, temperature, provider_name, extra_headers=None, tools=None):
        now = time.time()
        last_error = None
        if provider_name == "custom":
            for k in keys:
                self.key_cooldowns.pop(f"{provider_name}:{k}", None)
        elif all(self.key_cooldowns.get(f"{provider_name}:{k}", 0) > now for k in keys):
            for k in keys:
                self.key_cooldowns.pop(f"{provider_name}:{k}", None)

        async with aiohttp.ClientSession() as session:
            for api_key in keys:
                cd_key = f"{provider_name}:{api_key}"
                if provider_name != "custom" and self.key_cooldowns.get(cd_key, 0) > now:
                    continue
                headers = {
                    "Content-Type": "application/json",
                }
                if api_key and api_key != "dummy":
                    headers["Authorization"] = f"Bearer {api_key}"
                if extra_headers:
                    headers.update(extra_headers)
                payload = {
                    "model": model,
                    "messages": messages,
                    "temperature": min(float(temperature), 2.0),
                    "max_tokens": 4096,
                }
                if tools:
                    payload["tools"] = tools
                    payload["tool_choice"] = "auto"
                for attempt in range(2):
                    try:
                        async with session.post(
                            url,
                            headers=headers,
                            json=payload,
                            timeout=aiohttp.ClientTimeout(total=GEMINI_TIMEOUT),
                        ) as resp:
                            text = await resp.text()
                            if resp.status == 402 and attempt == 0:
                                try:
                                    err_msg = json.loads(text).get("error", {}).get("message", text)
                                    match = re.search(r"can only afford (\d+)", err_msg)
                                    if match:
                                        payload["max_tokens"] = max(1, int(match.group(1)))
                                        continue
                                except Exception:
                                    pass
                            if resp.status == 429:
                                if provider_name != "custom":
                                    self._set_key_cooldown(cd_key, 3600)
                                last_error = ConnectionError(f"{provider_name} 429: rate limited")
                                break
                            if resp.status in (401, 403):
                                if provider_name != "custom":
                                    self._set_key_cooldown(cd_key, 86400 * 365)
                                last_error = ConnectionError(f"{provider_name} {resp.status}: invalid key")
                                break
                            if resp.status != 200:
                                fg = None
                                try:
                                    ej = json.loads(text).get("error", {})
                                    err_msg = ej.get("message", text) if isinstance(ej, dict) else text
                                    if isinstance(ej, dict):
                                        fg = ej.get("failed_generation")
                                except Exception:
                                    err_msg = text[:200]
                                last_error = ConnectionError(f"{provider_name} {resp.status}: {err_msg}")
                                try: last_error.failed_generation = fg
                                except Exception: pass
                                break
                            try:
                                result = json.loads(text)
                            except json.JSONDecodeError:
                                raise ValueError(f"{provider_name} returned non-JSON: {text[:200]}")
                            if "choices" not in result or not result["choices"]:
                                if "error" in result:
                                    raise ValueError(f"{provider_name} error: {result['error']}")
                                raise ValueError(f"{provider_name} empty response")
                            message_obj = result["choices"][0].get("message", {})
                            content = message_obj.get("content", "")
                            if isinstance(content, list):
                                content = "\n".join(str(p.get("text", p)) for p in content)
                            if tools:
                                # режим инструментов: вернуть полное сообщение (content может быть пустым при tool_calls)
                                if not str(content or "").strip() and not message_obj.get("tool_calls"):
                                    raise ValueError(f"{provider_name} empty content")
                                return message_obj, result.get("usage", {})
                            if not str(content).strip():
                                raise ValueError(f"{provider_name} empty content")
                            return str(content).strip(), result.get("usage", {})
                    except (aiohttp.ClientError, asyncio.TimeoutError) as e:
                        last_error = ConnectionError(f"{provider_name} connection error ({url}): {e}")
                        break
        if last_error:
            raise last_error
        raise ValueError(f"Все ключи {self._provider_label(provider_name)} недоступны или исчерпали квоту.")

    async def _call_google_rest(self, model_name: str, prompt: str, input_image_bytes=None):
        keys = self._get_sorted_keys()
        if not keys: return {"error": {"message": "Нет доступных API ключей"}}
        parts = [{"text": prompt}]
        if input_image_bytes:
            resized = await utils.run_sync(self._resize_image_ig, input_image_bytes)
            b64_img = base64.b64encode(resized).decode('utf-8')
            parts.insert(0, {"inlineData": {"mimeType": "image/jpeg", "data": b64_img}})
        payload = {
            "contents": [{"parts": parts}],
            "safetySettings": [
                {"category": cat, "threshold": "BLOCK_NONE"}
                for cat in ["HARM_CATEGORY_HARASSMENT", "HARM_CATEGORY_HATE_SPEECH", "HARM_CATEGORY_SEXUALLY_EXPLICIT", "HARM_CATEGORY_DANGEROUS_CONTENT"]
            ],
            "generationConfig": {"candidateCount": 1, "temperature": 1.0}
        }
        proxy = self.config['proxy'] if self.config['proxy'] else None
        last_error = None
        async with aiohttp.ClientSession() as session:
            for i, api_key in enumerate(keys):
                url = f"https://generativelanguage.googleapis.com/v1beta/models/{model_name}:generateContent?key={api_key}"
                try:
                    if i > 0: await asyncio.sleep(1)
                    async with session.post(url, json=payload, proxy=proxy, timeout=60) as resp:
                        if resp.status == 200:
                            return await resp.json()
                        elif resp.status in [429, 503, 403]:
                            last_error = f"HTTP {resp.status}"
                            continue
                        else:
                            text = await resp.text()
                            return {"error": {"message": f"HTTP {resp.status}: {text}"}}
                except Exception as e:
                    last_error = str(e)
                    continue
        return {"error": {"message": f"All keys exhausted. Last error: {last_error}"}}

    def _resize_image_ig(self, img_bytes):
        try:
            img = Image.open(io.BytesIO(img_bytes))
            img.thumbnail((1024, 1024)) 
            out = io.BytesIO()
            if img.mode in ("RGBA", "P"): img = img.convert("RGB")
            img.save(out, format='JPEG', quality=85)
            return out.getvalue()
        except: return img_bytes

    # =========================================================================
    # Обработка ошибок
    # =========================================================================

    def _handle_error(self, e: Exception) -> str:
        logger.exception("Gemini execution error")
        if isinstance(e, asyncio.TimeoutError):
            return self.strings["api_timeout"]
        if isinstance(e, RuntimeError) and "Все ключи исчерпали" in str(e):
            return self.strings["all_keys_exhausted"].format(len(self.api_keys))
        if google_exceptions and isinstance(e, google_exceptions.GoogleAPIError):
            msg = str(e)
            if "quota" in msg.lower() or "exceeded" in msg.lower():
                return f"▲ <b>Превышен лимит API.</b>\n<code>{utils.escape_html(msg)}</code>"
            if "API key not valid" in msg:
                return self.strings["invalid_api_key"]
            if "blocked" in msg.lower():
                return self.strings["blocked_error"].format(utils.escape_html(msg))
            return self.strings["api_error"].format(utils.escape_html(msg))
        if isinstance(e, (OSError, aiohttp.ClientError, socket.timeout)):
            return "▲ <b>Сетевая ошибка:</b>\n<code>{}</code>".format(utils.escape_html(str(e)))
        return self.strings["generic_error"].format(utils.escape_html(str(e)))

    # =========================================================================
    # Подготовка запроса (медиа)
    # =========================================================================

    async def _prepare_parts(self, message: Message, custom_text: str=None):
        final_parts, warnings = [], []
        prompt_text_chunks = []
        user_args = custom_text if custom_text is not None else utils.get_args_raw(message)
        try:
            chat = await message.get_chat()
            chat_title = getattr(chat, 'title', getattr(chat, 'first_name', 'Личные сообщения'))
        except Exception:
            chat_title = "Неизвестный чат"
        prompt_text_chunks.append(f"[System info: We are in '{chat_title}' chat]")
        reply = await message.get_reply_message()
        if reply and getattr(reply, "text", None):
            try:
                reply_sender = await reply.get_sender()
                reply_author_name = get_display_name(reply_sender) if reply_sender else "Unknown"
                prompt_text_chunks.append(f"{reply_author_name}: {reply.text}")
            except Exception: 
                prompt_text_chunks.append(f"Ответ на: {reply.text}")
        try:
            current_sender = await message.get_sender()
            current_user_name = get_display_name(current_sender) if current_sender else "User"
            prompt_text_chunks.append(f"{current_user_name}: {user_args or ''}")
        except Exception: 
            prompt_text_chunks.append(f"Запрос: {user_args or ''}")
        media_source = message if message.media or message.sticker else reply
        has_media = bool(media_source and (media_source.media or media_source.sticker))
        if has_media:
            if media_source.sticker and hasattr(media_source.sticker, 'mime_type') and media_source.sticker.mime_type=='application/x-tgsticker':
                alt_text = next((attr.alt for attr in media_source.sticker.attributes if isinstance(attr, DocumentAttributeSticker)), "?")
                prompt_text_chunks.append(f"[Анимированный стикер: {alt_text}]")
            else:
                media, mime_type, filename = media_source.media, "application/octet-stream", "file"
                if media_source.photo: 
                    mime_type = "image/jpeg"
                elif hasattr(media_source, "document") and media_source.document:
                    mime_type = getattr(media_source.document, "mime_type", mime_type)
                    doc_attr = next((attr for attr in media_source.document.attributes if isinstance(attr, DocumentAttributeFilename)), None)
                    if doc_attr: filename = doc_attr.file_name
                    
                async def get_bytes(m):
                    bio = io.BytesIO()
                    await self.client.download_media(m, bio)
                    return bio.getvalue()
                    
                if mime_type.startswith("image/"):
                    try:
                        data = await get_bytes(media)
                        final_parts.append(types.Part(inline_data=types.Blob(mime_type=mime_type, data=data)))
                    except Exception as e: warnings.append(f"▲ Ошибка обработки изображения '{filename}': {e}")
                elif mime_type in self.TEXT_MIME_TYPES or filename.split('.')[-1] in ('txt', 'py', 'js', 'json', 'md', 'html', 'css', 'sh'):
                    try:
                        data = await get_bytes(media)
                        file_content = data.decode('utf-8')
                        prompt_text_chunks.insert(0, f"[Содержимое файла '{filename}']: \n```\n{file_content}\n```")
                    except Exception as e: warnings.append(f"▲ Ошибка чтения файла '{filename}': {e}")
                elif mime_type.startswith("audio/"):
                    input_path, output_path = None, None
                    try:
                        with tempfile.NamedTemporaryFile(suffix=f".{filename.split('.')[-1]}", delete=False) as temp_in: input_path = temp_in.name
                        await self.client.download_media(media, input_path)
                        if os.path.getsize(input_path) > MAX_FFMPEG_SIZE:
                            warnings.append(f"▲ Аудиофайл '{filename}' слишком большой."); raise StopIteration
                        with tempfile.NamedTemporaryFile(suffix=".mp3", delete=False) as temp_out: output_path = temp_out.name
                        ffmpeg_cmd = ["ffmpeg", "-y", "-i", input_path, "-c:a", "libmp3lame", "-q:a", "2", output_path]
                        process_ffmpeg = await asyncio.create_subprocess_exec(*ffmpeg_cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
                        await process_ffmpeg.communicate()
                        if process_ffmpeg.returncode != 0: raise Exception("FFmpeg error")
                        with open(output_path, "rb") as f:
                            final_parts.append(types.Part(inline_data=types.Blob(mime_type="audio/mpeg", data=f.read())))
                    except StopIteration: pass
                    except Exception as e: warnings.append(f"▲ Ошибка обработки аудио: {e}")
                    finally:
                        if input_path and os.path.exists(input_path): os.remove(input_path)
                        if output_path and os.path.exists(output_path): os.remove(output_path)
                elif mime_type.startswith("video/"):
                    input_path, output_path = None, None
                    try:
                        with tempfile.NamedTemporaryFile(suffix=f".{filename.split('.')[-1]}", delete=False) as temp_in: input_path = temp_in.name
                        await self.client.download_media(media, input_path)
                        if os.path.getsize(input_path) > MAX_FFMPEG_SIZE:
                            warnings.append(f"▲ Медиафайл '{filename}' слишком большой."); raise StopIteration
                        ffprobe_cmd = ["ffprobe", "-v", "error", "-select_streams", "a:0", "-show_entries", "stream=codec_type", "-of", "default=noprint_wrappers=1:nokey=1", input_path]
                        process_probe = await asyncio.create_subprocess_exec(*ffprobe_cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
                        stdout, _ = await process_probe.communicate()
                        has_audio = bool(stdout.strip())
                        with tempfile.NamedTemporaryFile(suffix=".mp4", delete=False) as temp_out: output_path = temp_out.name
                        ffmpeg_cmd = ["ffmpeg", "-y", "-i", input_path]
                        maps = ["-map", "0:v:0"]
                        if not has_audio:
                            ffmpeg_cmd.extend(["-f", "lavfi", "-i", "anullsrc=channel_layout=stereo:sample_rate=44100"])
                            maps.extend(["-map", "1:a:0"])
                        else:
                            maps.extend(["-map", "0:a:0?"])
                        ffmpeg_cmd.extend([*maps, "-vf", "pad=ceil(iw/2)*2:ceil(ih/2)*2", "-c:v", "libx264", "-c:a", "aac", "-pix_fmt", "yuv420p", "-movflags", "+faststart", "-shortest", output_path])
                        process_ffmpeg = await asyncio.create_subprocess_exec(*ffmpeg_cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
                        _, stderr = await process_ffmpeg.communicate()
                        if process_ffmpeg.returncode != 0:
                            stderr_str = stderr.decode()
                            warnings.append(f"▲ <b>Ошибка FFmpeg:</b>\nНе удалось конвертировать '{filename}'. Детали:\n<code>{utils.escape_html(stderr_str)}</code>")
                            raise StopIteration
                        with open(output_path, "rb") as f:
                            final_parts.append(types.Part(inline_data=types.Blob(mime_type="video/mp4", data=f.read())))
                    except StopIteration: pass
                    except Exception as e: warnings.append(f"▲ Ошибка обработки видео: {e}")
                    finally:
                        if input_path and os.path.exists(input_path): os.remove(input_path)
                        if output_path and os.path.exists(output_path): os.remove(output_path)
                        
        if not user_args and has_media and not final_parts and not any("[Содержимое файла" in chunk for chunk in prompt_text_chunks):
            prompt_text_chunks.append(self.strings["media_reply_placeholder"])
        full_prompt_text = "\n".join(chunk for chunk in prompt_text_chunks if chunk and chunk.strip()).strip()
        if full_prompt_text:
            final_parts.insert(0, types.Part(text=full_prompt_text))
        return final_parts, warnings

    async def _get_recent_chat_text(self, cid, count=None, skip_last=False):
        lim = (count or self.config["impersonation_history_limit"]) + (1 if skip_last else 0)
        lines = []
        try:
            msgs = await self.client.get_messages(cid, limit=lim)
            if skip_last and msgs: msgs = msgs[1:]
            for m in msgs:
                if not m: continue
                if not (m.text or m.sticker or m.photo or m.file or m.media):
                    continue
                name = get_display_name(await m.get_sender()) or "Unknown"
                txt = m.text or ""
                if m.sticker:
                    alt = "?"
                    if hasattr(m.sticker, 'attributes'):
                        alt = next((a.alt for a in m.sticker.attributes if isinstance(a, DocumentAttributeSticker)), "?")
                    txt += f" [Стикер: {alt}]"
                elif m.photo:
                    txt += " [Фото]"
                elif m.file:
                    txt += " [Файл]"
                elif m.media and not txt:
                    txt += " [Медиа]"
                if txt.strip():
                    lines.append(f"{name}: {txt.strip()}")
        except Exception:
            pass 
        return "\n".join(reversed(lines))

    # =========================================================================
    # Команды
    # =========================================================================

    @loader.command()
    async def m(self, message: Message):
        """[текст или reply] — Отправить запрос к AI (поддерживает ссылки и медиа)."""
        clean_args = utils.get_args_raw(message)
        # --- локальный триггер "запомни ...": сразу сохраняем в навыки, без AI ---
        m_remember = re.match(r"(?i)^\s*запомни(?:\s+навсегда|\s+пожалуйста)?\s*[:\-,]?\s*(.+)$", clean_args or "", re.S)
        if m_remember:
            fact = m_remember.group(1).strip()
            if fact:
                # имя = первые 3 слова, транслит-недо, но для читаемости берём из текста
                base = re.sub(r"[^\w]+", "_", fact.lower())[:40].strip("_") or "fact"
                name = base
                i = 2
                while name in self.skills:
                    name = f"{base}_{i}"
                    i += 1
                self.skills[name] = fact
                self._save_skills()
                return await utils.answer(
                    message,
                    f"⏣ Запомнил навсегда: <b>{utils.escape_html(fact[:200])}</b>\n"
                    f"∅ Навык: <code>{utils.escape_html(name)}</code> · Всего: {len(self.skills)}\n"
                    f"<i>Удалить:</i> <code>.mskill del {utils.escape_html(name)}</code>"
                )
            return await utils.answer(message, "✗ Что именно запомнить? Напиши после «запомни».")
        reply = await message.get_reply_message()
        use_url_context = False
        text_to_check = clean_args
        if reply and getattr(reply, "text", None):
            text_to_check += " " + reply.text
        if re.search(r'https?://\S+', text_to_check): use_url_context = True
        status_msg = await utils.answer(message, self.strings["processing"])
        status_msg = await self.client.get_messages(status_msg.chat_id, ids=status_msg.id)
        parts, warnings = await self._prepare_parts(message, custom_text=clean_args)
        if warnings and status_msg:
            try: await status_msg.edit(f"{status_msg.text}\n\n" + "\n".join(warnings))
            except: pass
        if not parts:
            if status_msg: await utils.answer(status_msg, self.strings["no_prompt_or_media"])
            return
        await self._send_to_gemini(
            message=message, parts=parts, status_msg=status_msg,
            use_url_context=use_url_context, display_prompt=clean_args or None
        )

    @loader.command()
    async def g(self, message: Message):
        """[алиас]"""
        await self.m(message)

    @loader.command()
    async def mtools(self, message: Message):
        """[on/off] — Включить или отключить режим выполнения инструментов."""
        arg = utils.get_args_raw(message).strip().lower()
        if arg in ("on", "1", "true", "вкл", "вкл."):
            self.config["enable_tools"] = True
            return await utils.answer(message, self._maybe_clean_symbols(self.strings["tools_on"]))
        if arg in ("off", "0", "false", "выкл", "выкл."):
            self.config["enable_tools"] = False
            return await utils.answer(message, self._maybe_clean_symbols(self.strings["tools_off"]))
        state = "ВКЛ ✓" if self.config["enable_tools"] else "ВЫКЛ ✗"
        await utils.answer(message, self._maybe_clean_symbols(self.strings["tools_status"].format(
            state, self.config["tools_max_iters"], self.config["tools_shell_timeout"], self._provider_label()
        )))

    @loader.command()
    async def gtools(self, message: Message):
        """[алиас]"""
        await self.mtools(message)

    @loader.command()
    async def mt(self, message: Message):
        """[текст или reply] — Запрос к AI с выполнением инструментов (терминал, код, Telegram)."""
        if not self.config["enable_tools"]:
            state = "ВЫКЛ ✗"
            return await utils.answer(message, self._maybe_clean_symbols(self.strings["tools_status"].format(
                state, self.config["tools_max_iters"], self.config["tools_shell_timeout"], self._provider_label()
            )))
        await self.m(message)

    @loader.command()
    async def gt(self, message: Message):
        """[алиас]"""
        await self.mt(message)

    @loader.command()
    async def mstat(self, message: Message):
        """— Показать статистику сессии (запросы, токены, память, провайдер)."""
        now = time.time()
        st = self.session_stats
        uptime = self._human_duration(now - float(st.get("start_time", now) or now))
        requests = int(st.get("requests", 0) or 0)
        t_in = int(st.get("tokens_in", 0) or 0)
        t_out = int(st.get("tokens_out", 0) or 0)
        times = [float(x) for x in (st.get("times", []) or [])]
        avg_t = sum(times) / len(times) if times else 0.0
        last_t = times[-1] if times else 0.0

        chats = len(self.conversations)
        pairs = sum(len(v) // 2 for v in self.conversations.values() if isinstance(v, list))
        gauto_chats = len(self.gauto_conversations)
        presets = len(self.prompt_presets)
        imp_chats = len(self.impersonation_chats)
        mem_off = len(self.memory_disabled_chats)
        g_keys = len(self.api_keys)
        cooldowns = sum(1 for t in self.key_cooldowns.values() if float(t or 0) > now)

        provider = self._normalize_provider_name()
        model = self._resolve_effective_model(provider, self.config["model_name"], [], "")
        configured = [
            self._provider_label(p) for p in self.CORE_PROVIDER_ORDER
            if (self.api_keys if p == "google" else self._keys_for(p)) or (p == "custom" and self.config.get("custom_base_url"))
        ]
        tools_state = "ВКЛ ✓" if self.config["enable_tools"] else "ВЫКЛ ✗"
        mem_mode = "◎ global" if self.config["global_memory"] else "по чатам"

        text = self.strings["gstat"].format(
            uptime=uptime,
            requests=requests,
            t_in=f"{t_in:,}".replace(",", " "),
            t_out=f"{t_out:,}".replace(",", " "),
            t_total=f"{t_in + t_out:,}".replace(",", " "),
            avg_t=round(avg_t, 1),
            last_t=round(last_t, 1),
            provider=utils.escape_html(self._provider_label(provider)),
            model=utils.escape_html(str(model)),
            profile=utils.escape_html(str(self.config["model_profile"])),
            g_keys=g_keys,
            cooldowns=cooldowns,
            configured=utils.escape_html(", ".join(configured) or "—"),
            chats=chats,
            pairs=pairs,
            gauto_chats=gauto_chats,
            imp_chats=imp_chats,
            mem_off=mem_off,
            mem_mode=mem_mode,
            presets=presets,
            tools_state=tools_state,
        )
        # разбивка по провайдерам
        by_provider = dict(st.get("by_provider", {}) or {})
        if by_provider:
            rows = sorted(by_provider.items(), key=lambda kv: -int(kv[1].get("tokens", 0) or 0))
            lines = ["", "∷ <b>По провайдерам</b> (запросы · токены):"]
            for pname, pdata in rows:
                lines.append(
                    f"• <b>{utils.escape_html(self._provider_label(pname))}:</b> "
                    f"{int(pdata.get('requests', 0) or 0)} req · {(int(pdata.get('tokens', 0) or 0)):,} tok".replace(",", " ")
                )
            text += "\n" + "\n".join(lines)
        if self.skills:
            text += f"\n\n⏣ <b>Навыков:</b> {len(self.skills)} (вечная память, см. <code>.mskill</code>)"
        await utils.answer(message, self._maybe_clean_symbols(text))

    @loader.command()
    async def gstat(self, message: Message):
        """[алиас]"""
        await self.mstat(message)

    # =========================================================================
    # KeyTest — валидатор API-ключей (интегрирован из @kgpix KeyTest)
    # =========================================================================
    def _all_keys(self, text):
        if not text:
            return []
        out, seen = [], set()
        for tok in re.findall(r"[A-Za-z0-9_\-\.:]{16,}", text):
            if tok in seen or _detect(tok)[0] == "none":
                continue
            seen.add(tok)
            out.append(tok)
        return out

    async def _resolve(self, session, key, sem):
        mode, ids = _detect(key)
        if mode == "none":
            return None
        if mode == "single" and "method" not in SPECS[ids[0]]:
            return (ids[0], _R("unsupported"))
        if mode == "loose":
            ids = LOOSE + (DEEP_EXTRA if self.config["kt_deep"] else [])
        timeout = int(self.config["kt_timeout"])

        async def guarded(pid):
            async with sem:
                try:
                    return pid, await _check_one(pid, session, key, timeout)
                except Exception as e:  # noqa: BLE001
                    return pid, _R("error", None, None, str(e)[:60])

        pairs = await asyncio.gather(*[guarded(pid) for pid in ids])
        if mode == "single":
            return pairs[0]
        for pid, res in pairs:
            if res["verdict"] in ("valid", "no_balance", "rate_limited"):
                return (pid, res)
        return None

    def _vword(self, verdict):
        return self.strings.get("v_" + verdict, verdict)

    def _loc_units(self, s):
        """Localize the English unit words produced by balance parsers."""
        if not s:
            return s
        for en, key in (("credits", "u_credits"), ("chars", "u_chars"),
                        ("tokens", "u_tokens"), ("images", "u_images"),
                        ("debt", "u_debt"), ("org:", "u_org")):
            if en in s:
                s = s.replace(en, self.strings[key])
        return s

    def _format_single(self, pid, data):
        verdict = data["verdict"]
        lines = ["<b>%s</b> %s" % (self.strings["l_status"], self._vword(verdict))]
        if verdict in ("valid", "no_balance", "rate_limited"):
            if self.config["kt_show_model"] and data.get("model") and data["model"] != "-":
                lines.append("<b>%s</b> %s" % (self.strings["l_model"], utils.escape_html(str(data["model"]))))
            if data.get("balance"):
                lines.append("<b>%s</b> %s" % (self.strings["l_balance"], utils.escape_html(self._loc_units(str(data["balance"])))))
        if data.get("info"):
            lines.append(utils.escape_html(str(data["info"])))
        if self.config["kt_show_detail"] and data.get("detail"):
            lines.append("<b>%s</b> %s" % (self.strings["l_note"], utils.escape_html(str(data["detail"]))))
        return "<b>%s</b>\n<blockquote expandable>%s</blockquote>" % (
            utils.escape_html(NAMES.get(pid, pid)), "\n".join(lines))

    def _multi_entry(self, key, result):
        """Return (block, text): block in valid|invalid|error, text = key + module answer."""
        kcode = "<code>%s</code>" % utils.escape_html(key)
        if result is None:
            return "invalid", "%s\n%s" % (kcode, self.strings["m_unknown"])
        pid, data = result
        v = data["verdict"]
        block = ("no_balance" if v == "no_balance"
                 else "valid" if v in ("valid", "rate_limited")
                 else "invalid" if v in ("invalid", "forbidden")
                 else "error")
        parts = [utils.escape_html(NAMES.get(pid, pid))]
        if v not in ("valid", "invalid", "no_balance"):  # block header already conveys these
            parts.append(self._vword(v))
        if data.get("balance"):
            parts.append(utils.escape_html(self._loc_units(str(data["balance"]))))
        if data.get("info"):
            parts.append(utils.escape_html(str(data["info"])))
        return block, "%s\n%s" % (kcode, " · ".join(parts))

    def _results_to_text(self, groups, extra):
        """Plain-text version of results for .txt file output."""
        _strip = re.compile(r"<[^>]+>")
        _ents = (("&lt;", "<"), ("&gt;", ">"), ("&amp;", "&"))
        def clean(s):
            s = _strip.sub("", s)
            for e, r in _ents:
                s = s.replace(e, r)
            return s.strip()
        lines = []
        for block, label in (("valid",      "blk_valid"),
                              ("no_balance", "blk_no_balance"),
                              ("invalid",    "blk_invalid"),
                              ("error",      "blk_error")):
            if not groups[block]:
                continue
            lines.append("[%s (%d)]" % (self.strings[label], len(groups[block])))
            for entry in groups[block]:
                lines.append(clean(entry))
            lines.append("")
        if extra:
            lines.append(self.strings["more"].format(extra))
        return "\n".join(lines).strip()

    @loader.command(
        ru_doc="[ключ] | проверить API-ключ(и) AI-провайдера по реплаю",
        kk_doc="[кілт] | реплай арқылы AI-провайдердің API-кілт(тер)ін тексеру",
    )
    async def keytest(self, message):
        """[key] | check an AI provider API key (or many) by reply or file"""
        args = utils.get_args_raw(message)
        source = args

        if not source:
            reply = await message.get_reply_message()
            if reply:
                if reply.document or reply.photo:
                    # ---- file support ----
                    doc = reply.document
                    if doc and doc.size > 2 * 1024 * 1024:
                        await utils.answer(
                            message,
                            "<blockquote>%s</blockquote>" % self.strings["file_too_big"],
                        )
                        return
                    message = await utils.answer(message, self.strings["file_reading"])
                    try:
                        raw = await reply.download_media(bytes)
                        source = raw.decode("utf-8", errors="ignore")
                        if not source.strip():
                            for enc in ("utf-16", "latin-1", "cp1251"):
                                try:
                                    source = raw.decode(enc, errors="ignore")
                                    if source.strip():
                                        break
                                except Exception:  # noqa: BLE001
                                    continue
                    except Exception as e:  # noqa: BLE001
                        await utils.answer(
                            message,
                            "<blockquote>%s</blockquote>"
                            % self.strings["file_bad_enc"],
                        )
                        return
                elif reply.raw_text:
                    source = reply.raw_text

        keys = self._all_keys(source)
        if not keys:
            await utils.answer(message, "<blockquote>%s</blockquote>" % self.strings["no_key"])
            return

        extra = 0
        if len(keys) > 30:
            extra, keys = len(keys) - 30, keys[:30]

        message = await utils.answer(
            message,
            self.strings["checking"] if len(keys) == 1 else self.strings["checking_n"].format(len(keys)))

        sem = asyncio.Semaphore(14)
        try:
            async with _make_session(self.config["kt_proxy"]) as session:
                results = await asyncio.gather(*[self._resolve(session, k, sem) for k in keys])
        except (ValueError, RuntimeError) as e:
            await utils.answer(message, "<b>%s</b>\n<blockquote expandable>%s</blockquote>"
                               % (self.strings["proxy_err"], utils.escape_html(str(e)[:200])))
            return
        except Exception as e:  # noqa: BLE001
            await utils.answer(message, "<b>%s</b>\n<blockquote expandable>%s</blockquote>"
                               % (self.strings["v_error"], utils.escape_html(str(e)[:120])))
            return

        if len(keys) == 1:
            res = results[0]
            if res is None:
                await utils.answer(message, "<blockquote expandable>%s</blockquote>" % self.strings["unknown"])
            else:
                formatted_text = self._format_single(res[0], res[1])
                pid, data = res
                verdict = data.get("verdict")
                prov = "google" if pid == "google" else pid
                if verdict in ("valid", "rate_limited") and prov in self.CORE_PROVIDER_ORDER:
                    if not hasattr(self, "_pending_keys") or not isinstance(self._pending_keys, dict):
                        self._pending_keys = {}
                    k_id = uuid.uuid4().hex[:8]
                    now = time.time()
                    self._pending_keys = {k: v for k, v in self._pending_keys.items() if now - v.get("time", 0) < 3600}
                    self._pending_keys[k_id] = {
                        "key": keys[0],
                        "provider": prov,
                        "time": now,
                    }
                    buttons = [
                        [
                            {"text": f"✓ Сохранить для {self._provider_label(prov)}", "data": f"gemini:kt_apply:{k_id}:save"},
                            {"text": "✓ Сохранить и включить", "data": f"gemini:kt_apply:{k_id}:act"},
                        ]
                    ]
                    try:
                        return await self.inline.form(text=formatted_text, message=message, reply_markup=buttons)
                    except Exception:
                        return await utils.answer(message, formatted_text)
                await utils.answer(message, formatted_text)
            return

        groups = {"valid": [], "no_balance": [], "invalid": [], "error": []}
        for k, r in zip(keys, results):
            block, line = self._multi_entry(k, r)
            groups[block].append(line)

        blocks = []
        for block, label in (("valid", "blk_valid"), ("no_balance", "blk_no_balance"),
                             ("invalid", "blk_invalid"), ("error", "blk_error")):
            if groups[block]:
                blocks.append("<b>%s (%d)</b>\n<blockquote expandable>%s</blockquote>"
                              % (self.strings[label], len(groups[block]), "\n\n".join(groups[block])))
        if extra:
            blocks.append(self.strings["more"].format(extra))

        out = "\n".join(blocks)
        if len(out) > 3500:
            import io
            txt = self._results_to_text(groups, extra)
            buf = io.BytesIO(txt.encode("utf-8"))
            buf.name = self.strings["results_file"]
            await utils.answer_file(message, buf)
        else:
            await utils.answer(message, out)

    @loader.command(
        ru_doc="| проверить текущий прокси",
        kk_doc="| ағымдағы проксіні тексеру",
    )
    async def kproxytest(self, message):
        """| test current proxy"""
        from urllib.parse import urlparse  # noqa: PLC0415
        proxy = (self.config.get("kt_proxy") or "").strip()
        if not proxy:
            return
        p = urlparse(proxy)
        has_creds = bool(p.username)
        # With creds:    scheme://***@host   (hide creds + port, show host)
        # Without creds: scheme://***        (hide everything — public/borrowed proxy)
        if has_creds:
            masked = "%s://***@%s" % (p.scheme, p.hostname or "")
        else:
            masked = "%s://***" % p.scheme
        message = await utils.answer(message, self.strings["proxy_testing"])
        t0 = time.perf_counter_ns()
        try:
            async with _make_session(proxy) as session:
                async with session.get(
                    "https://api.ipify.org?format=json",
                    timeout=aiohttp.ClientTimeout(total=10),
                ) as r:
                    ms = (time.perf_counter_ns() - t0) // 1_000_000
                    if r.status == 200:
                        ip = (await r.json(content_type=None)).get("ip", "?")
                        lines = [
                            "<b>%s</b> %s" % (self.strings["l_proxy_url"], utils.escape_html(masked)),
                        ]
                        if has_creds:
                            lines.append("<b>%s</b> %s" % (self.strings["l_proxy_ip"], utils.escape_html(ip)))
                        lines.append("<b>%s</b> %s ms" % (self.strings["l_proxy_ms"], ms))
                        await utils.answer(
                            message,
                            "<b>%s</b>\n<blockquote expandable>%s</blockquote>"
                            % (self.strings["proxy_ok"], "\n".join(lines)),
                        )
                    else:
                        await utils.answer(
                            message,
                            "<b>%s</b>\n<blockquote expandable>HTTP %d</blockquote>"
                            % (self.strings["proxy_err"], r.status),
                        )
        except Exception as e:  # noqa: BLE001
            await utils.answer(
                message,
                "<b>%s</b>\n<blockquote expandable>%s</blockquote>"
                % (self.strings["proxy_err"], utils.escape_html(str(e)[:200])),
            )

    @loader.command(
        ru_doc="[тип] | список провайдеров (без аргумента — сводка по типам)",
        kk_doc="[түр] | провайдерлер тізімі (аргументсіз — түрлер бойынша қысқаша)",
    )
    async def kprov(self, message):
        """[type] | list providers (no arg = summary by type)"""
        arg = utils.get_args_raw(message).strip().lower()
        checkable = sum(1 for s in SPECS.values() if "method" in s)
        if arg in CATS:
            names = sorted(s["n"] for s in SPECS.values() if s.get("cat") == arg)
            chk = sum(1 for s in SPECS.values() if s.get("cat") == arg and "method" in s)
            header = "<b>%s — %d · %s %d</b>" % (
                self.strings["cat_" + arg], len(names), self.strings["checkable"], chk)
            await utils.answer(message, "%s\n<blockquote expandable>%s</blockquote>"
                               % (header, utils.escape_html(", ".join(names))))
            return
        lines = []
        for c in CATS:
            n = sum(1 for s in SPECS.values() if s.get("cat") == c)
            if n:
                lines.append("<b>%s</b> <code>%s</code> — %d" % (self.strings["cat_" + c], c, n))
        header = "<b>%s: %d · %s %d</b>" % (
            self.strings["providers"], len(SPECS), self.strings["checkable"], checkable)
        await utils.answer(message, "%s\n<blockquote expandable>%s\n\n%s</blockquote>"
                           % (header, "\n".join(lines), self.strings["kprov_hint"]))

    @loader.command()
    async def mask(self, message: Message):
        """[текст или reply] — Быстрый вопрос без сохранения в контекст памяти."""
        clean_args = utils.get_args_raw(message)
        if not clean_args and not await message.get_reply_message():
            return await utils.answer(message, self.strings["gask_no_prompt"])
        status_msg = await utils.answer(message, self.strings["processing"])
        status_msg = await self.client.get_messages(status_msg.chat_id, ids=status_msg.id)
        parts, warnings = await self._prepare_parts(message, custom_text=clean_args)
        if warnings and status_msg:
            try: await status_msg.edit(f"{status_msg.text}\n\n" + "\n".join(warnings))
            except: pass
        if not parts:
            return await utils.answer(status_msg, self.strings["no_prompt_or_media"])
        await self._send_to_gemini(
            message=message,
            parts=parts,
            status_msg=status_msg,
            display_prompt=clean_args or None,
            ephemeral=True,
        )

    @loader.command()
    async def gask(self, message: Message):
        """[алиас]"""
        await self.mask(message)

    @loader.command()
    async def mmusic(self, message: Message):
        """<промпт> — Генерация музыки или аудио через Gemini Lyria."""
        args = utils.get_args_raw(message)
        if not args:
            return await utils.answer(message, "♫ <b>Введите промпт для генерации музыки.</b>\nПример: <code>.mmusic веселая мелодия на гитаре</code>")
        m = await utils.answer(message, "♫ <b>Генерация аудио...</b>")
        keys = self._get_sorted_keys()
        if not keys:
            return await utils.answer(m, self.strings["all_keys_exhausted"].format(len(self.api_keys)))
        audio_bytes = None
        lyrics_text = ""
        last_error = None
        for key in keys:
            try:
                client = genai.Client(api_key=key)
                interaction = await client.aio.interactions.create(
                    model="lyria-3-clip-preview",
                    input=args,
                )
                for output in getattr(interaction, "outputs", []) or []:
                    if getattr(output, "type", None) == "audio" and getattr(output, "data", None):
                        audio_bytes = base64.b64decode(output.data)
                    elif getattr(output, "type", None) == "text" and getattr(output, "text", None):
                        lyrics_text = output.text
                    if audio_bytes:
                        break
                raise ValueError("Модель не вернула аудио-данные.")
            except Exception as e:
                err_str = str(e).lower()
                if any(x in err_str for x in ("429", "quota", "exhausted")):
                    self._set_key_cooldown(key, self._extract_retry_delay_seconds(str(e), 3600))
                    self.key_model_map[key] = 0
                    self.db.set(self.strings["name"], DB_KEY_MAP_KEY, self.key_model_map)
                elif any(x in err_str for x in ("api key not valid", "api_key_invalid", "permission_denied", "client application")):
                    self._set_key_cooldown(key, 86400 * 365)
                    self.key_model_map[key] = -1
                    self.db.set(self.strings["name"], DB_KEY_MAP_KEY, self.key_model_map)
                last_error = e
                continue
        if not audio_bytes:
            return await utils.answer(m, f"▲ <b>Ошибка генерации музыки:</b> <code>{utils.escape_html(str(last_error or 'Не удалось получить аудио'))}</code>")
        out = io.BytesIO(audio_bytes)
        out.name = f"gemini_music_{uuid.uuid4().hex[:6]}.mp3"
        caption = f"♫ <b>Gemini Music (Lyria)</b>\n∅ <code>{utils.escape_html(args[:100])}</code>"
        if lyrics_text:
            caption += f"\n\n♫ <b>Текст:</b>\n<blockquote>{utils.escape_html(lyrics_text[:800])}</blockquote>"
        await self.client.send_file(
            utils.get_chat_id(message),
            out,
            caption=caption,
            reply_to=message.id,
            voice=True,
        )
        await m.delete()

    @loader.command()
    async def gmusic(self, message: Message):
        """[алиас]"""
        await self.mmusic(message)

    @loader.command()
    async def mimg(self, message: Message):
        """<промпт> [reply] — Генерация или редактирование изображений."""
        args = utils.get_args_raw(message)
        reply = await message.get_reply_message()
        input_bytes = None
        if reply:
            if reply.photo:
                input_bytes = await self.client.download_media(reply, bytes)
            elif reply.document and reply.document.mime_type.startswith("image/"):
                input_bytes = await self.client.download_media(reply, bytes)
        if not args and not input_bytes:
            return await utils.answer(message, "⬠ <b>Введите промпт.</b>\nПример: <code>.mimg кот в космосе</code>")
        prompt = args if args else "Describe/Modify this image"
        model = self.config["image_model_name"]
        m = await utils.answer(message, self.strings["gimg_process"].format(model=model))
        try:
            res = await self._call_google_rest(model, prompt, input_bytes)
            if "error" in res:
                err_msg = res["error"]["message"]
                try: err_msg = json.loads(err_msg)["error"]["message"]
                except: pass
                raise ValueError(err_msg)
            img_bytes = None
            if "candidates" not in res or not res["candidates"]:
                raise ValueError("API вернул пустой ответ (нет candidates).")
            candidate = res["candidates"][0]
            if "content" not in candidate:
                reason = candidate.get("finishReason", "Unknown")
                raise ValueError(f"Модель отказалась генерировать. Причина: {reason}")
            try:
                parts = candidate["content"].get("parts", [])
                for part in parts:
                    if "inlineData" in part:
                        img_bytes = base64.b64decode(part["inlineData"]["data"])
                        break
            except Exception as e:
                raise ValueError(f"Ошибка чтения данных картинки: {e}")
            if not img_bytes:
                raise ValueError("Модель не вернула изображение (возможно, сработал Safety Filter).")
            out = io.BytesIO(img_bytes)
            out.name = f"gemini_{uuid.uuid4().hex[:6]}.jpg"
            await self.client.send_file(
                utils.get_chat_id(message),
                out,
                caption=f"⬠ <b>Gemini Image</b>\n⌬ <code>{model}</code>\n∅ <code>{utils.escape_html(prompt[:100])}</code>",
                reply_to=message.id
            )
            await m.delete()
        except Exception as e:
            await utils.answer(m, f"▲ <b>Ошибка:</b>\n<code>{utils.escape_html(str(e))}</code>")

    @loader.command()
    async def gimg(self, message: Message):
        """[алиас]"""
        await self.mimg(message)

    @loader.command()
    async def mskey(self, message: Message):
        """[-h] — Проверить статус доступности API-ключей Gemini."""
        args = utils.get_args_raw(message).strip()
        if args in ["-h", "--having", "having"]:
            premium = sum(1 for v in self.key_model_map.values() if v == 1)
            free = sum(1 for v in self.key_model_map.values() if v == 0)
            report = (
                f"∷ <b>Статус ключей (кеш):</b>\n"
                f"◈ <b>Premium/Active:</b> {premium}\n"
                f"◇ <b>Free/Unknown:</b> {free}\n"
                f"⚿ <b>Всего в конфиге:</b> {len(self.api_keys)}"
            )
            return await utils.answer(message, report)
        await utils.answer(message, "◴ <b>Сканирую ключи...</b>\n<i>Это займет время (1.2 сек на ключ).</i>")
        report, invalid_keys = await self._scan_keys(force=True)
        if invalid_keys:
            txt_keys = "\n".join(invalid_keys)
            try:
                await self.client.send_message("me", f"▲ <b>magent: Найдены невалидные ключи:</b>\nУдали их из конфига:\n\n<code>{txt_keys}</code>")
                report += "\n\n▲ <b>Список невалидных ключей отправлен в Избранное.</b>"
            except:
                report += "\n\n▲ <b>Найдены невалидные ключи.</b>"
        await utils.answer(message, report)

    @loader.command()
    async def gskey(self, message: Message):
        """[алиас]"""
        await self.mskey(message)

    async def _scan_keys(self, force=False):
        if not GOOGLE_AVAILABLE: return "Library missing", []
        current_map_keys = list(self.key_model_map.keys())
        for k in current_map_keys:
            if k not in self.api_keys: del self.key_model_map[k]
        if not force and all(k in self.key_model_map for k in self.api_keys):
            return "Loaded from cache", []
        if force: self.key_model_map = {}
        proxy_config = self._get_proxy_config()
        http_opts = types.HttpOptions(async_client_args={"proxies": proxy_config, "timeout": 10.0}) if proxy_config else None
        active_keys = []
        invalid_keys = []
        minimal_config = types.GenerateContentConfig(
            response_mime_type="text/plain",
            max_output_tokens=1, 
            candidate_count=1,
            safety_settings=[types.SafetySetting(category="HARM_CATEGORY_HARASSMENT", threshold="BLOCK_NONE")]
        )
        for i, key in enumerate(self.api_keys):
            if i > 0: await asyncio.sleep(1.2)
            try:
                client = genai.Client(api_key=key, http_options=http_opts)
                response = await client.aio.models.generate_content(
                    model=CHECK_MODEL, contents="test", config=minimal_config
                )
                active_keys.append(key)
                self.key_model_map[key] = 1
            except Exception as e:
                err = str(e).lower()
                if "invalid_argument" in err or "api_key_invalid" in err or "400" in err or "blocked" in err:
                    invalid_keys.append(key)
                    self.key_model_map[key] = -1
                else:
                    self.key_model_map[key] = 0 
        self.db.set(self.strings["name"], DB_KEY_MAP_KEY, self.key_model_map)
        short_report = (
            f"✓ <b>Скан завершен.</b>\n"
            f"◈ <b>Active:</b> {len(active_keys)}\n"
            f"⌫ <b>Invalid:</b> {len(invalid_keys)}\n"
            f"◇ <b>RateLimited/Other:</b> {len(self.api_keys) - len(active_keys) - len(invalid_keys)}"
        )
        return short_report, invalid_keys

    def _get_sorted_keys(self):
        valid_keys = []
        now = time.time()
        for key in self.api_keys:
            if self.key_cooldowns.get(str(key), 0) > now:
                continue
            if key not in self.key_model_map:
                valid_keys.append((key, 0, random.random()))
                continue
            tier = self.key_model_map[key]
            if tier == -1:
                continue
            valid_keys.append((key, tier, random.random()))
        valid_keys.sort(key=lambda x: (-x[1], x[2]))
        return [item[0] for item in valid_keys]

    @loader.command()
    async def mch(self, message: Message):
        """[id] <кол-во> <вопрос> — Проанализировать историю сообщений чата."""
        args_str = utils.get_args_raw(message)
        if not args_str: return await utils.answer(message, self.strings["gch_usage"])
        parts = args_str.split()
        target_chat_id = utils.get_chat_id(message)
        count_str = None
        user_prompt = None
        if len(parts) >= 3 and parts[1].isdigit():
            try:
                entity_arg = int(parts[0]) if parts[0].lstrip('-').isdigit() else parts[0]
                entity = await self.client.get_entity(entity_arg)
                target_chat_id = entity.id
                count_str = parts[1]
                user_prompt = " ".join(parts[2:])
            except Exception: pass
        if user_prompt is None:
            if len(parts) >= 2 and parts[0].isdigit():
                count_str = parts[0]
                user_prompt = " ".join(parts[1:])
            else: return await utils.answer(message, self.strings["gch_usage"])
        try: 
            count = int(count_str)
            if count <= 0 or count > 20000: raise ValueError
        except: return await utils.answer(message, "▲ Error: Count must be integer (1-20000).")
        status_msg = await utils.answer(message, self.strings["gch_processing"].format(count))
        try:
            entity = await self.client.get_entity(target_chat_id)
            chat_name = utils.escape_html(get_display_name(entity))
            chat_log = await self._get_recent_chat_text(target_chat_id, count=count, skip_last=False)
        except (ValueError, TypeError, ChatAdminRequiredError, UserNotParticipantError, ChannelPrivateError) as e:
            return await utils.answer(status_msg, self.strings["gch_chat_error"].format(target_chat_id, e.__class__.__name__))
        except Exception as e:
            return await utils.answer(status_msg, self.strings["gch_chat_error"].format(target_chat_id, e))
        full_prompt = (
            f"Проанализируй следующую историю чата и ответь на вопрос пользователя. "
            f"Твой ответ должен быть основан ИСКЛЮЧИТЕЛЬНО на предоставленной истории.\n\n"
            f"ВОПРОС ПОЛЬЗОВАТЕЛЯ: \"{user_prompt}\"\n\n"
            f"ИСТОРИЯ ЧАТА:\n---\n{chat_log}\n---"
        )
        header = self.strings["gch_result_caption_from_chat"].format(count, chat_name)
        full_prompt = f"{header}\n\n{full_prompt}"
        await self._send_to_gemini(
            message=message,
            parts=[types.Part(text=full_prompt)],
            status_msg=status_msg,
            display_prompt=f"{count} сообщений: {user_prompt}",
            ephemeral=True,
        )

    @loader.command()
    async def gch(self, message: Message):
        """[алиас]"""
        await self.mch(message)

    @loader.command()
    async def mprompt(self, message: Message):
        """<текст/-c/reply> — Установить или сбросить системную инструкцию."""
        args = utils.get_args_raw(message)
        reply = await message.get_reply_message()
        if args == "-c":
            self.config["system_instruction"] = ""
            return await utils.answer(message, self.strings["gprompt_cleared"])
        new_prompt = None
        preset = self._find_preset(args)
        if preset:
            new_prompt = preset['content']
        elif reply and reply.file:
            if reply.file.size > 1024 * 1024:
                return await utils.answer(message, self.strings["gprompt_file_too_big"])
            try:
                file_data = await self.client.download_file(reply.media, bytes)
                try: new_prompt = file_data.decode("utf-8")
                except UnicodeDecodeError: return await utils.answer(message, self.strings["gprompt_not_text"])
            except Exception as e:
                return await utils.answer(message, self.strings["gprompt_file_error"].format(e))
        elif args:
            new_prompt = args
        if new_prompt is not None:
            self.config["system_instruction"] = new_prompt
            return await utils.answer(message, self.strings["gprompt_updated"].format(len(new_prompt)))
        current_prompt = self.config["system_instruction"]
        if not current_prompt:
            return await utils.answer(message, self.strings["gprompt_usage"])
        if len(current_prompt) > 4000:
            file = io.BytesIO(current_prompt.encode("utf-8"))
            file.name = "system_instruction.txt"
            await utils.answer(message, self.strings["gprompt_current"], file=file)
        else:
            await utils.answer(message, f"{self.strings['gprompt_current']}\n<code>{utils.escape_html(current_prompt)}</code>")

    @loader.command()
    async def gprompt(self, message: Message):
        """[алиас]"""
        await self.mprompt(message)

    @loader.command()
    async def mauto(self, message: Message):
        """[on/off/id] — Включить или отключить автоответчик в чате."""
        args = utils.get_args_raw(message).split()
        if not args: return await utils.answer(message, self.strings["auto_mode_usage"])
        chat_id = utils.get_chat_id(message)
        state = args[0].lower()
        target = chat_id
        if len(args) == 2:
            try:
                e = await self.client.get_entity(args[0])
                target = e.id
                state = args[1].lower()
            except: return await utils.answer(message, self.strings["gauto_chat_not_found"].format(args[0]))
        if state == "on":
            self.impersonation_chats.add(target)
            self.db.set(self.strings["name"], DB_IMPERSONATION_KEY, list(self.impersonation_chats))
            txt = self.strings["auto_mode_on"].format(int(self.config["impersonation_reply_chance"]*100)) if target==chat_id else self.strings["gauto_state_updated"].format(f"<code>{target}</code>", self.strings["gauto_enabled"])
            await utils.answer(message, txt)
        elif state == "off":
            self.impersonation_chats.discard(target)
            self.db.set(self.strings["name"], DB_IMPERSONATION_KEY, list(self.impersonation_chats))
            txt = self.strings["auto_mode_off"] if target==chat_id else self.strings["gauto_state_updated"].format(f"<code>{target}</code>", self.strings["gauto_disabled"])
            await utils.answer(message, txt)
        else: await utils.answer(message, self.strings["auto_mode_usage"])

    @loader.command()
    async def gauto(self, message: Message):
        """[алиас]"""
        await self.mauto(message)

    @loader.command()
    async def mautochats(self, message: Message):
        """— Список чатов с активным автоответчиком."""
        if not self.impersonation_chats: return await utils.answer(message, self.strings["no_auto_mode_chats"])
        out = [self.strings["auto_mode_chats_title"].format(len(self.impersonation_chats))]
        for cid in self.impersonation_chats:
            try:
                e = await self.client.get_entity(cid)
                name = utils.escape_html(get_display_name(e))
                out.append(self.strings["memory_chat_line"].format(name, cid))
            except: out.append(self.strings["memory_chat_line"].format("Неизвестный чат", cid))
        await utils.answer(message, "\n".join(out))

    @loader.command()
    async def gautochats(self, message: Message):
        """[алиас]"""
        await self.mautochats(message)

    @loader.command()
    async def mclear(self, message: Message):
        """[global/auto] — Очистить историю диалога в текущем чате (auto — для mauto)."""
        args = utils.get_args_raw(message).lower()
        chat_id = utils.get_chat_id(message)
        if args == "global":
            if "global_context" in self.conversations:
                del self.conversations["global_context"]
                self._save_history_sync(False)
                await utils.answer(message, self.strings["memory_cleared_global"])
            else:
                await utils.answer(message, self.strings["gres_no_global"])
            return
        if args == "auto":
            if str(chat_id) in self.gauto_conversations:
                self._clear_history(chat_id, gauto=True)
                await utils.answer(message, self.strings["memory_cleared_gauto"])
            else:
                await utils.answer(message, self.strings["no_gauto_memory_to_clear"])
            return
        hist_key = "global_context" if self.config["global_memory"] else str(chat_id)
        if hist_key in self.conversations:
            self._clear_history(hist_key)
            keys_to_del = [k for k, v in self.pager_cache.items() if v.get("chat_id") == chat_id]
            for k in keys_to_del: del self.pager_cache[k]
            if keys_to_del: self.db.set(self.strings["name"], DB_PAGER_CACHE_KEY, self.pager_cache)
            await utils.answer(message, self.strings["memory_cleared_global"] if hist_key == "global_context" else self.strings["memory_cleared"])
        else:
            await utils.answer(message, self.strings["no_memory_to_clear"])

    @loader.command()
    async def gclear(self, message: Message):
        """[алиас]"""
        await self.mclear(message)

    @loader.command()
    async def mpresets(self, message: Message):
        """<save/load/del/list> — Управление сохраненными пресетами системных инструкций."""
        args = utils.get_args_raw(message)
        if not args: return await utils.answer(message, self.strings["gpresets_usage"])
        match = re.match(r"^(\w+)(?:\s+\[(.+?)\]|\s+(\S+))?(?:\s+(.*))?$", args, re.DOTALL)
        if not match: return await utils.answer(message, self.strings["gpresets_usage"])
        action = match.group(1).lower()
        name = match.group(2) or match.group(3)
        content = match.group(4)
        if action == "list":
            if not self.prompt_presets: return await utils.answer(message, self.strings["gpreset_empty"])
            text = self.strings["gpreset_list_head"]
            for idx, p in enumerate(self.prompt_presets, 1):
                text += f"<b>{idx}.</b> <code>{p['name']}</code> ({len(p['content'])} симв.)\n"
            return await utils.answer(message, text)
        if action == "save":
            if not name: return await utils.answer(message, "✗ Укажите имя: <code>.mpresets save [Имя] текст</code>")
            reply = await message.get_reply_message()
            if not content and reply:
                if reply.text: content = reply.text
                elif reply.file:
                    try: content = (await self.client.download_file(reply.media, bytes)).decode("utf-8", errors="ignore")
                    except: pass
            if not content: return await utils.answer(message, "✗ Нет текста для сохранения.")
            existing = self._find_preset(name)
            if existing:
                existing['content'] = content
            else:
                self.prompt_presets.append({"name": name, "content": content})
            self.db.set(self.strings["name"], DB_PRESETS_KEY, self.prompt_presets)
            await utils.answer(message, self.strings["gpreset_saved"].format(name, len(self.prompt_presets)))
        elif action == "load":
            target = self._find_preset(name)
            if not target: return await utils.answer(message, self.strings["gpreset_not_found"])
            self.config["system_instruction"] = target['content']
            await utils.answer(message, self.strings["gpreset_loaded"].format(target['name'], len(target['content'])))
        elif action == "del":
            target = self._find_preset(name)
            if not target: return await utils.answer(message, self.strings["gpreset_not_found"])
            self.prompt_presets.remove(target)
            self.db.set(self.strings["name"], DB_PRESETS_KEY, self.prompt_presets)
            await utils.answer(message, self.strings["gpreset_deleted"].format(target['name']))
        else:
             await utils.answer(message, self.strings["gpresets_usage"])

    @loader.command()
    async def gpresets(self, message: Message):
        """[алиас]"""
        await self.mpresets(message)

    def _find_preset(self, query):
        if not query: return None
        if str(query).isdigit():
            idx = int(query) - 1 
            if 0 <= idx < len(self.prompt_presets):
                return self.prompt_presets[idx]
        for p in self.prompt_presets:
            if p['name'].lower() == str(query).lower():
                return p
        return None

    @loader.command()
    async def mmemdel(self, message: Message):
        """[N] — Удалить последние N пар сообщений из истории диалога текущего чата."""
        try: n = int(utils.get_args_raw(message) or 1)
        except: n = 1
        cid = "global_context" if self.config["global_memory"] else utils.get_chat_id(message)
        hist = self._get_structured_history(cid)
        if n > 0 and len(hist) >= n*2:
            self.conversations[str(cid)] = hist[:-n*2]
            self._save_history_sync()
            await utils.answer(message, f"⌫ Удалено последних <b>{n}</b> пар сообщений из памяти.")
        else: await utils.answer(message, "Недостаточно истории для удаления.")

    @loader.command()
    async def gmemdel(self, message: Message):
        """[алиас]"""
        await self.mmemdel(message)

    @loader.command()
    async def mmemchats(self, message: Message):
        """— Список чатов с сохраненной историей диалогов."""
        if not self.conversations: return await utils.answer(message, self.strings["no_memory_found"])
        out = [self.strings["memory_chats_title"].format(len(self.conversations))]
        shown = set()
        for cid in list(self.conversations.keys()):
            if not str(cid).lstrip('-').isdigit(): continue
            chat_id = int(cid)
            if chat_id in shown: continue
            shown.add(chat_id)
            try:
                e = await self.client.get_entity(chat_id)
                name = get_display_name(e)
            except: name = f"Unknown ({chat_id})"
            out.append(self.strings["memory_chat_line"].format(name, chat_id))
        self._save_history_sync()
        if len(out) == 1: return await utils.answer(message, self.strings["no_memory_found"])
        await utils.answer(message, "\n".join(out))

    @loader.command()
    async def gmemchats(self, message: Message):
        """[алиас]"""
        await self.mmemchats(message)

    @loader.command()
    async def mmemexport(self, message: Message):
        """[id/auto] [-s] — Экспортировать историю диалогов в JSON-файл."""
        args = utils.get_args_raw(message).split()
        save_to_self = "-s" in args
        if save_to_self: args.remove("-s")
        gauto_mode = "auto" in args
        if gauto_mode: args.remove("auto")
        source_chat_id_str = args[0] if args else None
        target_chat_id = "me" if save_to_self else message.chat_id
        if source_chat_id_str:
            try:
                entity = await self.client.get_entity(
                    int(source_chat_id_str) if source_chat_id_str.lstrip("-").isdigit() else source_chat_id_str
                )
                source_chat_id = entity.id
                hist = self._get_structured_history(source_chat_id, gauto=gauto_mode)
            except Exception:
                await utils.answer(message, self.strings["gme_chat_not_found"].format(utils.escape_html(source_chat_id_str)))
                return
        else:
            source_chat_id = utils.get_chat_id(message)
            hist = self._get_structured_history(source_chat_id, gauto=gauto_mode)
        if not hist:
            await utils.answer(message, "История для экспорта пуста.")
            return
        user_ids = {e.get("user_id") for e in hist if e.get("role") == "user" and e.get("user_id")}
        user_names = {None: None}
        for uid in user_ids:
            if not uid: continue
            try:
                entity = await self.client.get_entity(uid)
                user_names[uid] = get_display_name(entity)
            except Exception: user_names[uid] = f"Deleted Account ({uid})"
        def make_serializable(entry):
            entry = dict(entry)
            user_id = entry.get("user_id")
            if user_id: entry["user_name"] = user_names.get(user_id)
            if isinstance(user_id, (int, str)): entry["user_id"] = user_id
            elif user_id is not None: entry["user_id"] = str(user_id)
            else: entry["user_id"] = None
            if "message_id" in entry and entry["message_id"] is not None:
                try: entry["message_id"] = int(entry["message_id"])
                except: entry["message_id"] = None
            return entry
        serializable_hist = [make_serializable(e) for e in hist]
        data = json.dumps(serializable_hist, ensure_ascii=False, indent=2)
        file_suffix = "gauto_history" if gauto_mode else "history"
        file = io.BytesIO(data.encode("utf-8"))
        file.name = f"magent_{file_suffix}_{source_chat_id}.json"
        caption = "Экспорт истории mauto magent" if gauto_mode else "Экспорт памяти magent"
        if source_chat_id != utils.get_chat_id(message):
            caption += f" из чата <code>{source_chat_id}</code>"
        await self.client.send_file(
            target_chat_id,
            file,
            caption=caption,
            reply_to=message.id if target_chat_id == message.chat_id else None,
        )
        if save_to_self:
            if target_chat_id == "me" and message.chat_id != self.me.id:
                 await utils.answer(message, self.strings["gme_sent_to_saved"])
            else:
                 await message.delete()

    @loader.command()
    async def gmemexport(self, message: Message):
        """[алиас]"""
        await self.mmemexport(message)

    @loader.command()
    async def mmemimport(self, message: Message):
        """[auto] [reply] — Импортировать историю диалогов из JSON-файла."""
        reply = await message.get_reply_message()
        if not reply or not reply.document: 
            return await utils.answer(message, "Ответьте на json-файл с памятью.")
        args = utils.get_args_raw(message).lower()
        gauto_mode = args == "auto"
        file = io.BytesIO()
        await self.client.download_media(reply, file)
        file.seek(0)
        MAX_IMPORT_SIZE = 15 * 1024 * 1024
        if file.getbuffer().nbytes > MAX_IMPORT_SIZE: 
            return await utils.answer(message, f"Файл слишком большой (>{MAX_IMPORT_SIZE // (1024*1024)} МБ).")
        try:
            hist = json.load(file)
            if not isinstance(hist, list): raise ValueError("Файл не содержит список истории.")
            new_hist = []
            for e in hist:
                if not isinstance(e, dict) or "role" not in e or "content" not in e: 
                    raise ValueError("Некорректная структура памяти.")
                entry = {
                    "role": e["role"], 
                    "type": e.get("type", "text"), 
                    "content": e["content"], 
                    "date": e.get("date")
                }
                if e["role"] == "user":
                    entry["user_id"] = e.get("user_id")
                    entry["message_id"] = e.get("message_id")
                new_hist.append(entry)
            chat_id = str(utils.get_chat_id(message))
            if gauto_mode:
                self.gauto_conversations[chat_id] = new_hist
                self._save_history_sync(gauto=True)
            else:
                self.conversations[chat_id] = new_hist
                self._save_history_sync(gauto=False)
            mem_type = "Mauto память" if gauto_mode else "Память"
            await utils.answer(message, f"✓ {mem_type} успешно импортирована ({len(new_hist)//2} диалогов).")
        except Exception as e:
            await utils.answer(message, f"▲ Ошибка импорта: {e}")

    @loader.command()
    async def gmemimport(self, message: Message):
        """[алиас]"""
        await self.mmemimport(message)

    @loader.command()
    async def mmemfind(self, message: Message):
        """<текст> — Поиск фрагментов по истории диалога в текущем чате."""
        q = utils.get_args_raw(message).lower()
        if not q: return await utils.answer(message, "Укажите слово для поиска.")
        cid = "global_context" if self.config["global_memory"] else utils.get_chat_id(message)
        hist = self._get_structured_history(cid)
        found = [f"{e['role']}: {e.get('content','')[:200]}" for e in hist if q in str(e.get('content','')).lower()]
        if not found: await utils.answer(message, "Ничего не найдено.")
        else: await utils.answer(message, "\n\n".join(found[:10]))

    @loader.command()
    async def gmemfind(self, message: Message):
        """[алиас]"""
        await self.mmemfind(message)

    @loader.command()
    async def mmemoff(self, message: Message):
        """— Отключить сохранение контекста в текущем чате."""
        self.memory_disabled_chats.add(str(utils.get_chat_id(message)))
        self.db.set(self.strings["name"], DB_MEMORY_DISABLED_KEY, list(self.memory_disabled_chats))
        await utils.answer(message, "Память в этом чате отключена.")

    @loader.command()
    async def gmemoff(self, message: Message):
        """[алиас]"""
        await self.mmemoff(message)

    @loader.command()
    async def mmemon(self, message: Message):
        """— Включить сохранение контекста в текущем чате."""
        self.memory_disabled_chats.discard(str(utils.get_chat_id(message)))
        self.db.set(self.strings["name"], DB_MEMORY_DISABLED_KEY, list(self.memory_disabled_chats))
        await utils.answer(message, "Память в этом чате включена.")

    @loader.command()
    async def gmemon(self, message: Message):
        """[алиас]"""
        await self.mmemon(message)

    @loader.command()
    async def mmemshow(self, message: Message):
        """[auto] — Просмотреть сохраненную историю диалога текущего чата."""
        args = utils.get_args_raw(message).lower()
        gauto = "auto" in args
        cid = "global_context" if ("global" in args or (self.config["global_memory"] and not gauto)) else utils.get_chat_id(message)
        hist = self._get_structured_history(cid, gauto=gauto)
        if not hist: return await utils.answer(message, "Память пуста.")
        out = []
        for e in hist[-40:]:
            role = e.get('role')
            content = utils.escape_html(str(e.get('content',''))[:300])
            if role == 'user': out.append(f"{content}")
            elif role == 'model': out.append(f"<b>AI:</b> {content}")
        await utils.answer(message, "<blockquote expandable='true'>" + "\n".join(out) + "</blockquote>")

    @loader.command()
    async def gmemshow(self, message: Message):
        """[алиас]"""
        await self.mmemshow(message)

    def _save_skills(self):
        self.db.set(self.strings["name"], DB_SKILLS_KEY, self.skills)

    @loader.command()
    async def mskill(self, message: Message):
        """[list/add/show/del/clear] — Управление постоянными навыками и правилами AI."""
        args = utils.get_args_raw(message).strip()
        low = args.lower()
        if not args or low in ("list", "список"):
            if not self.skills:
                return await utils.answer(message, "⏣ Навыков пока нет.\nДобавить: <code>.mskill add имя текст</code>\nПример: <code>.mskill add стиль Отвечай кратко, по-русски, с юмором</code>")
            lines = [f"⏣ <b>Постоянные навыки ({len(self.skills)}):</b>"]
            for i, (name, content) in enumerate(self.skills.items(), 1):
                preview = utils.escape_html(content[:150]) + ("…" if len(content) > 150 else "")
                lines.append(f"{i}. <b>{utils.escape_html(name)}</b>\n<blockquote expandable='true'>{preview}</blockquote>")
            lines.append("\n+ <code>.mskill add имя текст</code> · ⌫ <code>.mskill del имя</code> · ⌫ <code>.mskill clear</code>")
            return await utils.answer(message, "\n".join(lines))
        if low in ("clear", "очистить", "сброс"):
            count = len(self.skills)
            self.skills = {}
            self._save_skills()
            return await utils.answer(message, f"⌫ Удалено навыков: {count}.")
        if low in ("export", "экспорт"):
            if not self.skills:
                return await utils.answer(message, "Навыков нет — экспортировать нечего.")
            payload = json.dumps(self.skills, ensure_ascii=False, indent=2).encode("utf-8")
            f = io.BytesIO(payload)
            f.name = f"magent_skills_{int(time.time())}.json"
            await self.client.send_file(message.chat_id, f, caption=f"⏣ Экспорт навыков: {len(self.skills)} шт. Импорт: реплаем на этот файл <code>.mskill import</code>", reply_to=message.id)
            return
        if low in ("import", "импорт"):
            reply = await message.get_reply_message()
            if not (reply and reply.document):
                return await utils.answer(message, "Ответь этой командой на файл JSON: <code>.mskill import</code> (reply на файл из <code>.mskill export</code>)")
            try:
                raw = await reply.download_media(bytes)
                data = json.loads(raw.decode("utf-8", errors="ignore"))
                if not isinstance(data, dict):
                    raise ValueError("ожидается JSON-объект")
                added = 0
                for k, v in data.items():
                    if str(v).strip():
                        self.skills[str(k)] = str(v)
                        added += 1
                self._save_skills()
                return await utils.answer(message, f"✓ Импортировано навыков: {added}. Всего: {len(self.skills)}.")
            except Exception as e:
                return await utils.answer(message, f"▲ Ошибка импорта: {utils.escape_html(str(e)[:200])}")
        if low.startswith(("del ", "rm ", "удал ")):
            name = args.split(None, 1)[1].strip()
            if name in self.skills:
                del self.skills[name]
                self._save_skills()
                return await utils.answer(message, f"⌫ Навык <b>{utils.escape_html(name)}</b> удалён.")
            return await utils.answer(message, f"✗ Навык <b>{utils.escape_html(name)}</b> не найден.")
        if low.startswith(("show ", "показ ")):
            name = args.split(None, 1)[1].strip()
            if name in self.skills:
                return await utils.answer(message, f"∅ <b>{utils.escape_html(name)}</b>:\n<blockquote expandable='true'>{utils.escape_html(self.skills[name])}</blockquote>")
            return await utils.answer(message, f"✗ Навык <b>{utils.escape_html(name)}</b> не найден.")
        parts = args.split(None, 2)
        if len(parts) >= 3 and parts[0].lower() in ("add", "set", "доб", "учить"):
            _, name, content = parts
        elif len(parts) >= 2:
            name, content = parts[0], parts[1]
        else:
            return await utils.answer(message, "Использование:\n<code>.mskill add имя текст</code> — добавить/обновить\n<code>.mskill list</code> — список\n<code>.mskill show имя</code> — показать\n<code>.mskill del имя</code> — удалить\n<code>.mskill clear</code> — удалить всё")
        name = name.strip()
        content = content.strip()
        if not name or not content:
            return await utils.answer(message, "✗ Нужны и имя, и текст: <code>.mskill add имя текст</code>")
        existed = name in self.skills
        self.skills[name] = content
        self._save_skills()
        verb = "обновлён" if existed else "добавлен"
        await utils.answer(message, f"✓ Навык <b>{utils.escape_html(name)}</b> {verb} — буду помнить всегда ⏣")

    @loader.command()
    async def gskill(self, message: Message):
        """[алиас]"""
        await self.mskill(message)

    @loader.command()
    async def mteach(self, message: Message):
        """<имя> <описание> — Быстро обучить AI новому постоянному правилу."""
        await self.mskill(message)

    @loader.command()
    async def gteach(self, message: Message):
        """[алиас]"""
        await self.mskill(message)

    async def _show_providers_interactive_card(self, entity):
        current_provider = self._normalize_provider_name()
        effective = self._resolve_effective_model(current_provider, self.config["model_name"], [], "")
        has_key = bool(self._resolve_provider_api_key(current_provider)) or (current_provider == "custom" and bool(self.config.get("custom_base_url")))
        status_key = "✓ Настроен" if has_key else "▲ Не настроен"
        
        text = (
            "⬡ <b>Выбор провайдера API</b>\n\n"
            f"• <b>Текущий:</b> <code>{self._provider_label(current_provider)}</code>\n"
            f"• <b>Активная модель:</b> <code>{utils.escape_html(effective)}</code>\n"
            f"• <b>API Ключ:</b> {status_key}\n"
            f"• <b>Профиль:</b> <code>{utils.escape_html(str(self.config['model_profile']))}</code> · <b>Auto:</b> <code>{'on' if self.config['auto_model'] else 'off'}</code>\n\n"
            "<i>▼ Нажмите на провайдера для мгновенного переключения:</i>"
        )
        
        buttons = []
        row = []
        for prov in self.CORE_PROVIDER_ORDER:
            label = self._provider_label(prov)
            mark = "✓ " if prov == current_provider else ""
            row.append({"text": f"{mark}{label}", "data": f"gemini:prov:set:{prov}"})
            if len(row) == 2:
                buttons.append(row)
                row = []
        if row:
            buttons.append(row)
            
        buttons.append([
            {"text": f"∅ Модели {self._provider_label(current_provider)}", "data": f"gemini:prov:models:{current_provider}"},
            {"text": "⌖ Настройка профиля", "data": "gemini:prov:profile"},
        ])
        buttons.append([
            {"text": "✗ Закрыть", "data": "gemini:close:prov"}
        ])
        
        text = self._maybe_clean_symbols(text)
        if self.config.get("clean_symbols_mode", False):
            for r in buttons:
                for b in r:
                    b["text"] = self._clean_symbols_filter(b.get("text", ""))
        try:
            if isinstance(entity, Message):
                await self.inline.form(text=text, message=entity, reply_markup=buttons)
            elif isinstance(entity, InlineCall):
                await entity.edit(text=text, reply_markup=buttons)
        except Exception:
            if isinstance(entity, Message):
                await utils.answer(entity, text)

    async def _show_profiles_interactive_card(self, entity):
        current_profile = str(self.config.get("model_profile", "manual")).lower()
        provider = self._normalize_provider_name()
        effective = self._resolve_effective_model(provider, self.config["model_name"], [], "")
        
        profile_descriptions = {
            "auto": "Умный авто-подбор под текст запроса",
            "balanced": "Баланс качества, скорости и цены",
            "fast": "Максимальная скорость ответа",
            "reasoning": "Глубокие рассуждения (thinking)",
            "coding": "Специализация на коде и разработке",
            "vision": "Мультимодальность / зрение / медиа",
            "manual": "Фиксированная модель (без авто-смены)",
        }
        desc = profile_descriptions.get(current_profile, "")
        
        text = (
            "⌖ <b>Профиль авто-подбора модели</b>\n\n"
            f"• <b>Текущий профиль:</b> <code>{current_profile}</code> ({desc})\n"
            f"• <b>Auto-model:</b> <code>{'on' if self.config['auto_model'] else 'off'}</code>\n"
            f"• <b>Провайдер:</b> <code>{self._provider_label(provider)}</code>\n"
            f"• <b>Сейчас выберет:</b> <code>{utils.escape_html(effective)}</code>\n\n"
            "<i>▼ Выберите профиль для переключения:</i>"
        )
        
        buttons = []
        row = []
        for prof in MODEL_PROFILE_CHOICES:
            mark = "✓ " if prof == current_profile else ""
            row.append({"text": f"{mark}{prof}", "data": f"gemini:prof:set:{prof}"})
            if len(row) == 2:
                buttons.append(row)
                row = []
        if row:
            buttons.append(row)
            
        buttons.append([
            {"text": "∅ Модели (.mmodels)", "data": "gemini:prof:models"},
            {"text": "⬡ Провайдеры (.mprovider)", "data": "gemini:prov:menu"},
        ])
        buttons.append([
            {"text": "✗ Закрыть", "data": "gemini:close:prof"}
        ])
        
        text = self._maybe_clean_symbols(text)
        if self.config.get("clean_symbols_mode", False):
            for r in buttons:
                for b in r:
                    b["text"] = self._clean_symbols_filter(b.get("text", ""))
        try:
            if isinstance(entity, Message):
                await self.inline.form(text=text, message=entity, reply_markup=buttons)
            elif isinstance(entity, InlineCall):
                await entity.edit(text=text, reply_markup=buttons)
        except Exception:
            if isinstance(entity, Message):
                await utils.answer(entity, text)

    async def _show_model_interactive_card(self, entity):
        provider = self._normalize_provider_name()
        provider_config_keys = self.PROVIDER_MODEL_CFG
        cfg_key = provider_config_keys.get(provider)
        provider_specific = self.config.get(cfg_key, "") if cfg_key else ""
        effective = self._resolve_effective_model(provider, self.config["model_name"], [], "")
        def_mod = self._provider_default_model(provider)
        extra = f"\n∅ <b>Модель для {self._provider_label(provider)}:</b> <code>{utils.escape_html(str(provider_specific) or f'— (по умолчанию: {def_mod})')}</code>" if (cfg_key and provider != "google") else ""
        
        text = (
            f"⌘ <b>Провайдер:</b> <code>{self._provider_label(provider)}</code>\n"
            f"⌬ <b>Основная модель:</b> <code>{utils.escape_html(str(self.config['model_name']))}</code>{extra}\n"
            f"⌖ <b>Эффективная модель:</b> <code>{utils.escape_html(effective)}</code>\n"
            f"⌖ <b>Профиль:</b> <code>{utils.escape_html(str(self.config['model_profile']))}</code> · <b>Auto:</b> <code>{'on' if self.config['auto_model'] else 'off'}</code>\n\n"
            f"<i>▼ Быстрые действия:</i>"
        )
        buttons = [
            [{"text": f"∅ Выбрать модель {self._provider_label(provider)}", "data": f"gemini:gmod:quick_models:{provider}"}],
            [
                {"text": "⬡ Сменить провайдера", "data": "gemini:prov:menu"},
                {"text": "⌖ Настроить профиль", "data": "gemini:prof:menu"},
            ],
            [{"text": "✗ Закрыть", "data": "gemini:close:model"}],
        ]
        text = self._maybe_clean_symbols(text)
        if self.config.get("clean_symbols_mode", False):
            for r in buttons:
                for b in r:
                    b["text"] = self._clean_symbols_filter(b.get("text", ""))
        try:
            if isinstance(entity, Message):
                await self.inline.form(text=text, message=entity, reply_markup=buttons)
            elif isinstance(entity, InlineCall):
                await entity.edit(text=text, reply_markup=buttons)
        except Exception:
            await utils.answer(entity, text)

    @loader.command()
    async def mprovider(self, message: Message):
        """[провайдер] — Просмотр или переключение активного AI-провайдера."""
        args = utils.get_args_raw(message).strip().lower()
        if not args:
            return await self._show_providers_interactive_card(message)
        provider = self._normalize_provider_name(args)
        if provider not in self.CORE_PROVIDER_ORDER:
            return await utils.answer(message, self.strings["gprovider_usage"])
        prev = self._normalize_provider_name()
        self._remember_provider_model(prev, self.config["model_name"], manual=not self.config["auto_model"])
        self.config["provider"] = provider
        self.db.set(self.strings["name"], DB_PROVIDER_STATE_KEY, provider)
        restored = self._restore_provider_model(provider)
        effective = self._resolve_effective_model(provider, restored, [], "")
        await utils.answer(message, self.strings["gprovider_set"].format(self._provider_label(provider), utils.escape_html(effective)))

    @loader.command()
    async def gprovider(self, message: Message):
        """[алиас]"""
        return await self.mprovider(message)

    @loader.command()
    async def mprofile(self, message: Message):
        """[профиль] — Выбор профиля авто-подбора модели (auto, balanced, fast, coding и др.)."""
        args = utils.get_args_raw(message).strip().lower()
        provider = self._normalize_provider_name()
        if not args:
            return await self._show_profiles_interactive_card(message)
        if args not in MODEL_PROFILE_CHOICES:
            return await utils.answer(message, self.strings["gprofile_usage"])
        self.config["model_profile"] = args
        self.config["auto_model"] = args != "manual"
        effective = self._resolve_effective_model(provider, self.config["model_name"], [], "")
        self._remember_provider_model(provider, effective, manual=args == "manual")
        await utils.answer(message, self.strings["gprofile_set"].format(utils.escape_html(args), utils.escape_html(effective)))

    @loader.command()
    async def gprofile(self, message: Message):
        """[алиас]"""
        return await self.mprofile(message)

    @loader.command()
    async def mmodel(self, message: Message):
        """[модель] [-s] — Просмотр или ручная смена активной модели."""
        args_raw = utils.get_args_raw(message).strip()
        args = args_raw.lower()
        provider = self._normalize_provider_name()
        if args in ("-s", "--s", "s", "list"):
            return await self.mmodels(message)
        if not args_raw: 
            return await self._show_model_interactive_card(message)
        provider_config_keys = self.PROVIDER_MODEL_CFG
        cfg_key = provider_config_keys.get(provider)
        if cfg_key:
            self.config[cfg_key] = args_raw
        else:
            self.config["model_name"] = args_raw
        self.config["model_profile"] = "manual"
        self.config["auto_model"] = False
        self._remember_provider_model(provider, args_raw, manual=True)
        warning = ""
        if not self._model_matches_provider(args_raw, provider):
            warning = (
                "\n\n▲ <b>Возможна несовместимость.</b>\n"
                f"Модель <code>{utils.escape_html(args_raw)}</code> может не поддерживаться провайдером <b>{self._provider_label(provider)}</b>.\n"
                "Если не работает, смените провайдера: <code>.mprovider</code>"
            )
        await utils.answer(message, f"✓ Модель установлена: <code>{utils.escape_html(args_raw)}</code>\n⌖ Авто-подбор переключен в <code>manual</code>. Вернуть: <code>.mprofile auto</code>{warning}")

    @loader.command()
    async def gmodel(self, message: Message):
        """[алиас]"""
        return await self.mmodel(message)

    @loader.command()
    async def mrich(self, message: Message):
        """[on/off] — Переключить Rich Mode (спойлеры <details>, блоки размышлений, таблицы)."""
        args = utils.get_args_raw(message).strip().lower()
        if not args:
            status = "включен ✓" if self.config.get("rich_mode", True) else "выключен ✗"
            return await utils.answer(
                message,
                f"⬡ <b>Telegram Rich Mode</b>: {status}\n"
                "<i>Поддерживает нативные аккордеоны &lt;details&gt;, thinking-блоки модели, таблицы и расширенную разметку.</i>\n\n"
                "Использование: <code>.mrich on</code> или <code>.mrich off</code>"
            )
        if args in ("on", "1", "true", "вкл", "yes"):
            self.config["rich_mode"] = True
            await utils.answer(message, "✓ <b>Telegram Rich Mode включен!</b> Ответы будут форматироваться с нативными деталями и thinking-блоками.")
        elif args in ("off", "0", "false", "выкл", "no"):
            self.config["rich_mode"] = False
            await utils.answer(message, "✗ <b>Telegram Rich Mode выключен.</b> Используется классическая разметка blockquote.")
        else:
            await utils.answer(message, "Использование: <code>.mrich on</code> или <code>.mrich off</code>")

    @loader.command()
    async def grich(self, message: Message):
        """[алиас]"""
        return await self.mrich(message)

    @loader.command()
    async def mnoemoji(self, message: Message):
        """[on/off] — Переключить режим строгих текстовых символов вместо эмодзи."""
        args = utils.get_args_raw(message).strip().lower()
        if not args:
            cur = self.config.get("clean_symbols_mode", True)
            st = "включен ✓" if cur else "выключен ✗"
            return await utils.answer(
                message,
                self._maybe_clean_symbols(
                    f"∅ <b>Режим чистых символов (без эмодзи)</b>: {st}\n"
                    f"<i>Заменяет все эмодзи (обычные и Telegram Premium) на специальные Unicode-символы.</i>\n\n"
                    f"Использование: <code>.mnoemoji on</code> или <code>.mnoemoji off</code>"
                )
            )
        if args in ("on", "1", "true", "вкл", "yes"):
            self.config["clean_symbols_mode"] = True
            await utils.answer(
                message,
                self._maybe_clean_symbols(
                    "✓ <b>Режим чистых символов включен.</b> Все эмодзи заменяются на специальные Unicode-символы."
                )
            )
        elif args in ("off", "0", "false", "выкл", "no"):
            self.config["clean_symbols_mode"] = False
            await utils.answer(
                message,
                "✗ <b>Режим чистых символов выключен.</b>"
            )
        else:
            await utils.answer(message, "Использование: <code>.mnoemoji on</code> или <code>.mnoemoji off</code>")

    @loader.command()
    async def msymbols(self, message: Message):
        """[алиас]"""
        return await self.mnoemoji(message)

    @loader.command()
    async def gsymbols(self, message: Message):
        """[алиас]"""
        return await self.mnoemoji(message)

    @loader.command()
    async def gnoemoji(self, message: Message):
        """[алиас]"""
        return await self.mnoemoji(message)

    @loader.command()
    async def mmodels(self, message: Message):
        """[провайдер] [поиск] — Интерактивное меню каталога моделей с выбором по кнопке."""
        args_raw = utils.get_args_raw(message).strip()
        parts = args_raw.split(None, 1)
        current_prov = self._normalize_provider_name()
        target_provider = current_prov
        query = ""

        if parts:
            first = parts[0].lower()
            normalized = self._normalize_provider_name(first)
            if normalized in self.CORE_PROVIDER_ORDER:
                target_provider = normalized
                query = parts[1].strip() if len(parts) > 1 else ""
            else:
                query = args_raw

        status_msg = await utils.answer(
            message,
            f"◴ <b>Запрашиваю модели {self._provider_label(target_provider)} через API (curl)...</b>"
        )
        try:
            await self._show_provider_models_menu(status_msg, target_provider, query=query)
        except Exception as e:
            await utils.answer(status_msg, f"▲ <b>Ошибка загрузки каталога моделей:</b> {self._handle_error(e)}")

    @loader.command()
    async def gmodels(self, message: Message):
        """[алиас]"""
        return await self.mmodels(message)

    async def _show_provider_model_catalog(self, entity, provider: str):
        await self._show_provider_models_menu(entity, provider)

    async def _show_provider_models_menu(self, entity, provider: str, query: str = "", page: int = 0):
        provider = self._normalize_provider_name(provider)
        models, source_label, is_live = await self._fetch_provider_models_via_curl(provider)
        if not models:
            raise ValueError(self.strings.get("gmodel_no_models", "Не удалось получить список моделей."))

        filt = query.strip().lower()
        filtered = [m for m in models if filt in m.lower()] if filt else list(models)

        uid = uuid.uuid4().hex[:6]
        if not hasattr(self, "models_menu_cache") or not isinstance(self.models_menu_cache, dict):
            self.models_menu_cache = {}

        self.models_menu_cache[uid] = {
            "provider": provider,
            "raw_models": models,
            "models": filtered,
            "source_label": source_label,
            "is_live": is_live,
            "page": page,
            "filter": query.strip(),
            "chat_id": getattr(entity, "chat_id", 0),
            "msg_id": getattr(entity, "id", None),
            "time": time.time(),
        }
        await self._render_models_menu(uid, page, entity)

    async def _render_models_menu(self, uid: str, page: int, entity):
        data = getattr(self, "models_menu_cache", {}).get(uid)
        if not data:
            if isinstance(entity, InlineCall):
                await entity.edit(
                    "▲ <b>Сессия меню истекла.</b>\nВызовите <code>.mmodels</code> снова.",
                    reply_markup=[[{"text": "✗ Закрыть", "data": "gemini:close:expired"}]]
                )
            return

        provider = self._normalize_provider_name(data["provider"])
        models = data.get("models", [])
        total_items = len(models)
        raw_count = len(data.get("raw_models", []))
        source_label = data.get("source_label", "API")
        is_live = data.get("is_live", False)
        current_filter = data.get("filter", "")

        cfg_key = self.PROVIDER_MODEL_CFG.get(provider)
        active_model = self.config.get(cfg_key) if cfg_key else self.config.get("model_name")
        active_model = str(active_model or self._provider_default_model(provider)).strip()

        PAGE_SIZE = 6
        total_pages = max(1, (total_items + PAGE_SIZE - 1) // PAGE_SIZE)
        page = max(0, min(page, total_pages - 1))
        data["page"] = page

        start_idx = page * PAGE_SIZE
        end_idx = min(start_idx + PAGE_SIZE, total_items)
        page_models = models[start_idx:end_idx]

        buttons = []
        for i, m in enumerate(page_models, start=start_idx):
            is_active = (m == active_model)
            marker = "✓ " if is_active else "∅ "
            disp = m if len(m) <= 32 else m[:15] + "…" + m[-14:]
            buttons.append([{"text": f"{marker}{disp}", "data": f"gemini:gmod:set:{uid}:{i}"}])

        # Quick tag filters for providers with many models
        if raw_count > 15:
            filter_row = [
                {"text": "✦ Все" if current_filter else "Все", "data": f"gemini:gmod:flt:{uid}:all"},
                {"text": "Claude", "data": f"gemini:gmod:flt:{uid}:claude"},
                {"text": "GPT", "data": f"gemini:gmod:flt:{uid}:gpt"},
                {"text": "DeepSeek", "data": f"gemini:gmod:flt:{uid}:deepseek"},
                {"text": "Qwen", "data": f"gemini:gmod:flt:{uid}:qwen"},
            ]
            buttons.append(filter_row)

        # Pagination row
        if total_pages > 1:
            nav_row = []
            if page > 0:
                nav_row.append({"text": "◀️", "data": f"gemini:gmod:pg:{uid}:{page - 1}"})
            nav_row.append({"text": f"{page + 1}/{total_pages} ({total_items})", "data": "gemini:noop"})
            if page < total_pages - 1:
                nav_row.append({"text": "▶️", "data": f"gemini:gmod:pg:{uid}:{page + 1}"})
            buttons.append(nav_row)

        # Action row
        bottom_row = [
            {"text": "⬡ Провайдер", "data": f"gemini:gmod:prov_menu:{uid}"},
            {"text": "↺ Обновить (curl)", "data": f"gemini:gmod:ref:{uid}"},
            {"text": "✗ Закрыть", "data": f"gemini:close:{uid}"},
        ]
        buttons.append(bottom_row)

        status_dot = "●" if is_live else "◐"
        filter_str = f"\n⌕ <b>Фильтр:</b> <code>{utils.escape_html(current_filter)}</code> ({total_items} найдено)" if current_filter else ""
        text = (
            f"∅ <b>Каталог моделей: {self._provider_label(provider)}</b>\n"
            f"⌖ <b>Активная модель:</b> <code>{utils.escape_html(active_model)}</code>\n"
            f"⬡ <b>Источник:</b> {status_dot} {source_label} ({raw_count} всего){filter_str}\n"
            f"⌖ <b>Профиль:</b> <code>{utils.escape_html(str(self.config['model_profile']))}</code> · <b>Auto:</b> <code>{'on' if self.config['auto_model'] else 'off'}</code>\n\n"
            f"<i>▼ Нажмите на модель, чтобы переключить:</i>"
        )

        text = self._maybe_clean_symbols(text)
        if self.config.get("clean_symbols_mode", False):
            for r in buttons:
                for b in r:
                    b["text"] = self._clean_symbols_filter(b.get("text", ""))
        try:
            if isinstance(entity, Message):
                await self.inline.form(text=text, message=entity, reply_markup=buttons)
            elif isinstance(entity, InlineCall):
                await entity.edit(text=text, reply_markup=buttons)
            elif hasattr(entity, "edit"):
                await entity.edit(text=text, reply_markup=buttons)
        except Exception as e:
            logger.warning(f"Error rendering models menu: {e}")
            if isinstance(entity, Message):
                await utils.answer(entity, text)

    async def _render_providers_menu(self, uid: str, entity):
        data = getattr(self, "models_menu_cache", {}).get(uid)
        if not data:
            return
        current_provider = self._normalize_provider_name(data["provider"])
        providers = self.CORE_PROVIDER_ORDER
        buttons = []
        row = []
        for prov in providers:
            label = self._provider_label(prov)
            mark = "✓ " if prov == current_provider else ""
            row.append({"text": f"{mark}{label}", "data": f"gemini:gmod:prov_sel:{uid}:{prov}"})
            if len(row) == 2:
                buttons.append(row)
                row = []
        if row:
            buttons.append(row)
        buttons.append([
            {"text": "⬅️ Назад к моделям", "data": f"gemini:gmod:back:{uid}"},
            {"text": "✗ Закрыть", "data": f"gemini:close:{uid}"},
        ])
        text = (
            "⬡ <b>Выбор провайдера API</b>\n\n"
            f"Текущий активный: <b>{self._provider_label(current_provider)}</b>\n"
            "<i>Выберите провайдера для загрузки его моделей через API (curl):</i>"
        )
        if isinstance(entity, InlineCall):
            await entity.edit(text=text, reply_markup=buttons)
        elif hasattr(entity, "edit"):
            try: await entity.edit(text=text, reply_markup=buttons)
            except Exception: pass

    async def _get_provider_model_catalog(self, provider: str) -> list:
        models, _, _ = await self._fetch_provider_models_via_curl(provider)
        return models

    async def _fetch_provider_models_via_curl(self, provider: str, force_refresh: bool = False) -> tuple:
        provider = self._normalize_provider_name(provider)
        if not hasattr(self, "_provider_models_api_cache") or not isinstance(self._provider_models_api_cache, dict):
            self._provider_models_api_cache = {}

        if not force_refresh and provider in self._provider_models_api_cache:
            entry = self._provider_models_api_cache[provider]
            if time.time() - entry.get("time", 0) < 300:
                return entry["models"], entry["source_label"], entry["is_live"]

        raw_models = []
        source_label = ""
        is_live = False

        proxy = self.config.get("proxy") or None
        connector = None
        req_proxy = proxy
        if proxy and proxy.startswith(("socks4://", "socks5://", "http://", "https://")):
            try:
                from aiohttp_socks import ProxyConnector
                connector = ProxyConnector.from_url(proxy)
                req_proxy = None
            except Exception:
                req_proxy = proxy

        try:
            async with aiohttp.ClientSession(connector=connector) as session:
                # 1. Google Gemini
                if provider == "google":
                    keys = self._keys_for("google")
                    if keys:
                        for k in keys:
                            try:
                                url = f"https://generativelanguage.googleapis.com/v1beta/models?key={k}"
                                async with session.get(url, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                    if resp.status == 200:
                                        data = await resp.json()
                                        m_list = [
                                            m.get("name", "").split("/")[-1]
                                            for m in data.get("models", [])
                                            if "generateContent" in m.get("supportedGenerationMethods", ["generateContent"])
                                        ]
                                        if m_list:
                                            raw_models = sorted(m_list)
                                            source_label = "Google REST API (curl)"
                                            is_live = True
                                            break
                            except Exception:
                                continue
                    if not raw_models and GOOGLE_AVAILABLE and keys:
                        try:
                            client = genai.Client(api_key=keys[0])
                            models_obj = await asyncio.to_thread(client.models.list)
                            listed = sorted({m.name.split("/")[-1] for m in models_obj if getattr(m, "name", None)})
                            if listed:
                                raw_models = listed
                                source_label = "Google GenAI SDK"
                                is_live = True
                        except Exception:
                            pass

                # 2. OpenRouter
                elif provider == "openrouter":
                    keys = self._get_openrouter_keys()
                    headers = {"Authorization": f"Bearer {keys[0]}"} if keys else {}
                    headers["HTTP-Referer"] = "https://github.com/kgpix"
                    headers["X-Title"] = "Gemini Hikka Module"
                    url = "https://openrouter.ai/api/v1/models"
                    try:
                        async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=20)) as resp:
                            if resp.status == 200:
                                data = await resp.json()
                                items = [m.get("id") for m in data.get("data", []) if m.get("id")]
                                if items:
                                    raw_models = sorted(items)
                                    source_label = "OpenRouter API (curl)"
                                    is_live = True
                    except Exception as e:
                        logger.warning(f"OpenRouter models fetch error: {e}")

                # 3. OpenAI
                elif provider == "openai":
                    keys = self._get_openai_keys()
                    if keys:
                        for k in keys:
                            try:
                                url = "https://api.openai.com/v1/models"
                                headers = {"Authorization": f"Bearer {k}"}
                                async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                    if resp.status == 200:
                                        data = await resp.json()
                                        items = [m.get("id") for m in data.get("data", []) if m.get("id")]
                                        chat = [m for m in items if any(t in m.lower() for t in ("gpt", "o1", "o3", "chatgpt"))]
                                        others = [m for m in items if m not in chat and not any(t in m.lower() for t in ("whisper", "tts", "dall-e", "embedding", "moderation", "babbage", "davinci"))]
                                        raw_models = sorted(chat) + sorted(others)
                                        source_label = "OpenAI API (curl)"
                                        is_live = True
                                        break
                            except Exception:
                                continue

                # 4. DeepSeek
                elif provider == "deepseek":
                    keys = self._get_deepseek_keys()
                    if keys:
                        for k in keys:
                            try:
                                url = "https://api.deepseek.com/models"
                                headers = {"Authorization": f"Bearer {k}"}
                                async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                    if resp.status == 200:
                                        data = await resp.json()
                                        items = [m.get("id") for m in data.get("data", []) if m.get("id")]
                                        if items:
                                            raw_models = sorted(items)
                                            source_label = "DeepSeek API (curl)"
                                            is_live = True
                                            break
                            except Exception:
                                continue

                # 5. Groq
                elif provider == "groq":
                    keys = self._keys_for("groq")
                    if keys:
                        for k in keys:
                            try:
                                url = "https://api.groq.com/openai/v1/models"
                                headers = {"Authorization": f"Bearer {k}"}
                                async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                    if resp.status == 200:
                                        data = await resp.json()
                                        items = [m.get("id") for m in data.get("data", []) if m.get("id") and m.get("active", True)]
                                        if items:
                                            raw_models = sorted(items)
                                            source_label = "Groq API (curl)"
                                            is_live = True
                                            break
                            except Exception:
                                continue

                # 6. Mistral
                elif provider == "mistral":
                    keys = self._keys_for("mistral")
                    if keys:
                        for k in keys:
                            try:
                                url = "https://api.mistral.ai/v1/models"
                                headers = {"Authorization": f"Bearer {k}"}
                                async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                    if resp.status == 200:
                                        data = await resp.json()
                                        items = [m.get("id") for m in data.get("data", []) if m.get("id")]
                                        if items:
                                            raw_models = sorted(items)
                                            source_label = "Mistral API (curl)"
                                            is_live = True
                                            break
                            except Exception:
                                continue

                # 7. Together AI
                elif provider == "together":
                    keys = self._keys_for("together")
                    if keys:
                        for k in keys:
                            try:
                                url = "https://api.together.xyz/v1/models"
                                headers = {"Authorization": f"Bearer {k}"}
                                async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                    if resp.status == 200:
                                        data = await resp.json()
                                        items = data if isinstance(data, list) else data.get("data", [])
                                        chat = [m.get("id") for m in items if isinstance(m, dict) and m.get("id") and m.get("type") in ("chat", "language")]
                                        all_m = [m.get("id") for m in items if isinstance(m, dict) and m.get("id")]
                                        raw_models = sorted(chat) if chat else sorted(all_m)
                                        source_label = "Together AI API (curl)"
                                        is_live = True
                                        break
                            except Exception:
                                continue

                # 8. Cerebras
                elif provider == "cerebras":
                    keys = self._keys_for("cerebras")
                    if keys:
                        for k in keys:
                            try:
                                url = "https://api.cerebras.ai/v1/models"
                                headers = {"Authorization": f"Bearer {k}"}
                                async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                    if resp.status == 200:
                                        data = await resp.json()
                                        items = [m.get("id") for m in data.get("data", []) if m.get("id")]
                                        if items:
                                            raw_models = sorted(items)
                                            source_label = "Cerebras API (curl)"
                                            is_live = True
                                            break
                            except Exception:
                                continue

                # 9. xAI Grok
                elif provider == "xai":
                    keys = self._keys_for("xai")
                    if keys:
                        for k in keys:
                            try:
                                url = "https://api.x.ai/v1/models"
                                headers = {"Authorization": f"Bearer {k}"}
                                async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                    if resp.status == 200:
                                        data = await resp.json()
                                        items = [m.get("id") for m in data.get("data", []) if m.get("id")]
                                        if items:
                                            raw_models = sorted(items)
                                            source_label = "xAI Grok API (curl)"
                                            is_live = True
                                            break
                            except Exception:
                                continue

                # 10. Nvidia NIM
                elif provider == "nvidia":
                    keys = self._keys_for("nvidia")
                    if keys:
                        for k in keys:
                            try:
                                url = "https://integrate.api.nvidia.com/v1/models"
                                headers = {"Authorization": f"Bearer {k}"}
                                async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                    if resp.status == 200:
                                        data = await resp.json()
                                        items = [m.get("id") for m in data.get("data", []) if m.get("id")]
                                        if items:
                                            raw_models = sorted(items)
                                            source_label = "Nvidia NIM API (curl)"
                                            is_live = True
                                            break
                            except Exception:
                                continue

                # 11. HuggingFace
                elif provider == "huggingface":
                    keys = self._get_huggingface_keys()
                    headers = {"Authorization": f"Bearer {keys[0]}"} if keys else {}
                    # Try HF router first
                    try:
                        url = "https://router.huggingface.co/v1/models"
                        async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                            if resp.status == 200:
                                data = await resp.json()
                                items = [m.get("id") for m in data.get("data", []) if m.get("id")]
                                if items:
                                    raw_models = sorted(items)
                                    source_label = "HuggingFace Router API (curl)"
                                    is_live = True
                    except Exception:
                        pass
                    # If not, try HF hub API
                    if not raw_models:
                        try:
                            url = "https://huggingface.co/api/models?pipeline_tag=text-generation&sort=trendingScore&direction=-1&limit=80"
                            async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                if resp.status == 200:
                                    data = await resp.json()
                                    items = [m.get("id") for m in data if isinstance(m, dict) and m.get("id")]
                                    if items:
                                        raw_models = items
                                        source_label = "HuggingFace Hub API (curl)"
                                        is_live = True
                        except Exception:
                            pass

                # 12. Custom
                elif provider == "custom":
                    keys = self._keys_for("custom")
                    url = self._custom_models_endpoint()
                    if url:
                        headers = {"Authorization": f"Bearer {keys[0]}"} if keys else {}
                        try:
                            async with session.get(url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                                if resp.status == 200:
                                    data = await resp.json()
                                    items = []
                                    if isinstance(data, dict):
                                        if "data" in data and isinstance(data["data"], list):
                                            items = [m.get("id") for m in data["data"] if isinstance(m, dict) and m.get("id")]
                                        elif "models" in data and isinstance(data["models"], list):
                                            items = [m.get("name") or m.get("model") for m in data["models"] if isinstance(m, dict)]
                                    elif isinstance(data, list):
                                        items = [m.get("id") for m in data if isinstance(m, dict) and m.get("id")]
                                    if items:
                                        raw_models = sorted(items)
                                        source_label = f"{self._provider_label('custom')} API (curl)"
                                        is_live = True
                        except Exception as e:
                            logger.warning(f"Custom models fetch error: {e}")

                # 13. Other OpenAI compatible endpoints
                elif provider in self.OPENAI_COMPAT_ENDPOINTS:
                    chat_url = self.OPENAI_COMPAT_ENDPOINTS[provider]
                    models_url = chat_url.replace("/chat/completions", "/models")
                    keys = self._keys_for(provider)
                    headers = {"Authorization": f"Bearer {keys[0]}"} if keys else {}
                    try:
                        async with session.get(models_url, headers=headers, proxy=req_proxy, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                            if resp.status == 200:
                                data = await resp.json()
                                items = [m.get("id") for m in data.get("data", []) if isinstance(m, dict) and m.get("id")]
                                if items:
                                    raw_models = sorted(items)
                                    source_label = f"{self._provider_label(provider)} API (curl)"
                                    is_live = True
                    except Exception:
                        pass

        except Exception as e:
            logger.warning(f"Failed to fetch models for {provider}: {e}")

        # Deduplicate and sanitize
        clean = []
        seen = set()
        for m in raw_models:
            if not m:
                continue
            s = str(m).strip()
            if s and s not in seen:
                seen.add(s)
                clean.append(s)

        if not clean:
            clean = self._provider_curated_models(provider)
            source_label = "∅ Локальный каталог (без ключа / офлайн)"
            is_live = False

        self._provider_models_api_cache[provider] = {
            "models": clean,
            "source_label": source_label,
            "is_live": is_live,
            "time": time.time(),
        }
        return clean, source_label, is_live

    @loader.command()
    async def mres(self, message: Message):
        """[global/auto] — Полная очистка всей базы памяти диалогов (auto — для mauto)."""
        args = utils.get_args_raw(message).lower()
        if args == "global":
            if "global_context" in self.conversations:
                del self.conversations["global_context"]
                self._save_history_sync(False)
                await utils.answer(message, self.strings["gres_global_cleared"])
            else:
                await utils.answer(message, self.strings["gres_no_global"])
            return
        if args == "auto":
            if not self.gauto_conversations: return await utils.answer(message, self.strings["no_gauto_memory_to_fully_clear"])
            n = len(self.gauto_conversations)
            self.gauto_conversations.clear()
            self._save_history_sync(True)
            await utils.answer(message, self.strings["gauto_memory_fully_cleared"].format(n))
        elif not args:
            keys_to_delete = [k for k in self.conversations.keys() if k != "global_context"]
            if not keys_to_delete: return await utils.answer(message, self.strings["no_memory_to_fully_clear"])
            for key in keys_to_delete:
                del self.conversations[key]
            self._save_history_sync(False)
            await utils.answer(message, self.strings["memory_fully_cleared"].format(len(keys_to_delete)))
        else:
            await utils.answer(message, self.strings["gres_usage"])

    @loader.command()
    async def gres(self, message: Message):
        """[алиас]"""
        return await self.mres(message)

    @loader.callback_handler()
    async def gemini_callback_handler(self, call: InlineCall):
        if not (call.data.startswith("gemini:") or call.data.startswith("magent:")): return
        parts = call.data.split(":")
        action = parts[1]
        
        if action == "noop": 
            await call.answer()
            return
        if action == "close":
            uid = parts[2]
            if uid in self.pager_cache:
                del self.pager_cache[uid]
                self.db.set(self.strings["name"], DB_PAGER_CACHE_KEY, self.pager_cache)
            if hasattr(self, "models_menu_cache") and uid in self.models_menu_cache:
                del self.models_menu_cache[uid]
            try: await call.answer()
            except: pass
            try:
                chat = call.chat_id
                msg_id = call.message_id
                if chat and msg_id:
                    await self.client.delete_messages(chat, msg_id)
                else:
                    await call.delete()
            except Exception:
                try: await call.edit("⌫ <b>Сессия закрыта.</b>", reply_markup=None)
                except: pass
            return
        if action == "prov":
            sub = parts[2]
            if sub == "set":
                prov = parts[3]
                prev = self._normalize_provider_name()
                self._remember_provider_model(prev, self.config["model_name"], manual=not self.config["auto_model"])
                self.config["provider"] = prov
                self.db.set(self.strings["name"], DB_PROVIDER_STATE_KEY, prov)
                self._restore_provider_model(prov)
                try: await call.answer(f"⬡ Провайдер: {self._provider_label(prov)}")
                except: pass
                await self._show_providers_interactive_card(call)
                return
            if sub == "models":
                prov = parts[3] if len(parts) > 3 else self._normalize_provider_name()
                try: await call.answer("◴ Загружаю каталог моделей...")
                except: pass
                await self._show_provider_models_menu(call, prov)
                return
            if sub == "profile":
                try: await call.answer()
                except: pass
                await self._show_profiles_interactive_card(call)
                return
            if sub == "menu":
                try: await call.answer()
                except: pass
                await self._show_providers_interactive_card(call)
                return

        if action == "prof":
            sub = parts[2]
            if sub == "set":
                prof = parts[3]
                self.config["model_profile"] = prof
                self.db.set(self.strings["name"], DB_PROFILE_KEY, prof)
                if prof != "manual":
                    self.config["auto_model"] = True
                try: await call.answer(f"⌖ Профиль: {prof}")
                except: pass
                await self._show_profiles_interactive_card(call)
                return
            if sub == "models":
                prov = self._normalize_provider_name()
                try: await call.answer("◴ Загружаю каталог моделей...")
                except: pass
                await self._show_provider_models_menu(call, prov)
                return
            if sub == "menu":
                try: await call.answer()
                except: pass
                await self._show_profiles_interactive_card(call)
                return

        if action == "kt_apply":
            k_id = parts[2]
            mode = parts[3] if len(parts) > 3 else "save"
            data = getattr(self, "_pending_keys", {}).get(k_id)
            if not data:
                try: await call.answer("▲ Данные ключа истекли или уже сохранены.", show_alert=True)
                except: pass
                try: await call.edit("▲ <b>Данные ключа истекли.</b> Проверьте ключ заново через <code>.keytest</code>.", reply_markup=None)
                except: pass
                return
            prov = data.get("provider")
            api_key = data.get("key")
            cfg_key = PROVIDER_KEY_CFG.get(prov)
            if not cfg_key:
                try: await call.answer(f"▲ Не найден параметр конфига для {prov}", show_alert=True)
                except: pass
                return
            self.config[cfg_key] = api_key
            del self._pending_keys[k_id]

            status_text = f"✓ Ключ успешно сохранен в конфигурации (<code>{cfg_key}</code>)!"
            if mode == "act":
                prev = self._normalize_provider_name()
                self._remember_provider_model(prev, self.config["model_name"], manual=not self.config["auto_model"])
                self.config["provider"] = prov
                self.db.set(self.strings["name"], DB_PROVIDER_STATE_KEY, prov)
                self._restore_provider_model(prov)
                status_text += f"\n⬡ Провайдер автоматически переключен на <b>{self._provider_label(prov)}</b>."
                try: await call.answer(f"✓ Ключ сохранен и {self._provider_label(prov)} активирован!", show_alert=True)
                except: pass
            else:
                try: await call.answer(f"✓ Ключ для {self._provider_label(prov)} успешно сохранен!", show_alert=True)
                except: pass

            try:
                base_txt = call.text or ""
                await call.edit(
                    f"{base_txt}\n\n{status_text}",
                    reply_markup=[
                        [
                            {"text": f"∅ Модели {self._provider_label(prov)}", "data": f"gemini:gmod:quick_models:{prov}"},
                            {"text": "⬡ Провайдеры", "data": "gemini:prov:menu"},
                        ],
                        [{"text": "✗ Закрыть", "data": f"gemini:close:{k_id}"}],
                    ]
                )
            except Exception:
                try: await call.edit(status_text, reply_markup=None)
                except: pass
            return

        if action == "gmod":
            sub = parts[2]
            if sub == "quick_models":
                prov = parts[3] if len(parts) > 3 else self._normalize_provider_name()
                try: await call.answer("◴ Загружаю каталог моделей...")
                except: pass
                await self._show_provider_models_menu(call, prov)
                return
            uid = parts[3]
            data = getattr(self, "models_menu_cache", {}).get(uid)
            if not data:
                try: await call.answer("▲ Сессия меню устарела. Вызовите .mmodels снова.", show_alert=True)
                except: pass
                try: await call.edit("▲ <b>Сессия меню истекла.</b>\nВызовите <code>.mmodels</code> снова.", reply_markup=[[{"text": "✗ Закрыть", "data": f"gemini:close:{uid}"}]])
                except: pass
                return
            if sub == "set":
                try: idx = int(parts[4])
                except (ValueError, IndexError): return
                models = data.get("models", [])
                if idx < 0 or idx >= len(models):
                    await call.answer("▲ Модель не найдена.", show_alert=True)
                    return
                selected_model = models[idx]
                provider = data["provider"]
                cfg_key = self.PROVIDER_MODEL_CFG.get(provider)
                if cfg_key:
                    self.config[cfg_key] = selected_model
                else:
                    self.config["model_name"] = selected_model
                self.config["model_profile"] = "manual"
                self.config["auto_model"] = False
                self._remember_provider_model(provider, selected_model, manual=True)
                try: await call.answer(f"✓ Установлена модель: {selected_model}")
                except: pass
                await self._render_models_menu(uid, data.get("page", 0), call)
                return
            if sub == "pg":
                try: target_page = int(parts[4])
                except (ValueError, IndexError): target_page = 0
                await self._render_models_menu(uid, target_page, call)
                try: await call.answer()
                except: pass
                return
            if sub == "ref":
                provider = data["provider"]
                if hasattr(self, "_provider_models_api_cache") and provider in self._provider_models_api_cache:
                    del self._provider_models_api_cache[provider]
                try: await call.answer("◴ Запрашиваю модели через curl/API...")
                except: pass
                models, source_label, is_live = await self._fetch_provider_models_via_curl(provider, force_refresh=True)
                data["raw_models"] = models
                data["source_label"] = source_label
                data["is_live"] = is_live
                filt = data.get("filter", "")
                data["models"] = [m for m in models if filt.lower() in m.lower()] if filt else list(models)
                data["page"] = 0
                await self._render_models_menu(uid, 0, call)
                return
            if sub == "flt":
                tag = parts[4].lower()
                if tag in ("all", "clear"):
                    data["filter"] = ""
                    data["models"] = list(data["raw_models"])
                else:
                    data["filter"] = tag
                    data["models"] = [m for m in data["raw_models"] if tag in m.lower()]
                data["page"] = 0
                try: await call.answer(f"⌕ Фильтр: {tag} ({len(data['models'])} найдено)")
                except: pass
                await self._render_models_menu(uid, 0, call)
                return
            if sub == "prov_menu":
                await self._render_providers_menu(uid, call)
                try: await call.answer()
                except: pass
                return
            if sub == "prov_sel":
                new_prov = parts[4]
                prev = self._normalize_provider_name()
                self._remember_provider_model(prev, self.config["model_name"], manual=not self.config["auto_model"])
                self.config["provider"] = new_prov
                self.db.set(self.strings["name"], DB_PROVIDER_STATE_KEY, new_prov)
                self._restore_provider_model(new_prov)
                try: await call.answer(f"⬡ Провайдер: {self._provider_label(new_prov)}")
                except: pass
                models, source_label, is_live = await self._fetch_provider_models_via_curl(new_prov)
                data["provider"] = new_prov
                data["raw_models"] = models
                data["source_label"] = source_label
                data["is_live"] = is_live
                data["filter"] = ""
                data["models"] = list(models)
                data["page"] = 0
                await self._render_models_menu(uid, 0, call)
                return
            if sub == "back":
                await self._render_models_menu(uid, data.get("page", 0), call)
                try: await call.answer()
                except: pass
                return
        if action == "pg":
            uid = parts[2]
            page = int(parts[3])
            await self._render_page(uid, page, call)
            return
        if action in ("regen", "regen_att"):
            chat_id = int(parts[2])
            msg_id = int(parts[3])
            attempt = int(parts[4]) if action == "regen_att" and len(parts) > 4 else 1
            key = f"{chat_id}:{msg_id}"
            last_request_tuple = self.last_requests.get(key)
            if not last_request_tuple:
                await call.answer(self.strings["no_last_request"], show_alert=True)
                return
            last_parts, display_prompt = last_request_tuple
            use_url_context = bool(re.search(r'https?://\S+', display_prompt or ""))
            await call.edit(
                f"◴ <b>Регенерация (попытка {attempt})...</b>" if attempt > 1 else f"◴ <b>Регенерация...</b>",
                reply_markup=None,
            )
            await self._send_to_gemini(
                message=msg_id, 
                parts=last_parts, 
                regeneration=True, 
                call=call, 
                chat_id_override=chat_id, 
                use_url_context=use_url_context, 
                display_prompt=display_prompt,
                attempt=attempt,
            )
            return
        if action == "retry":
            chat_id = int(parts[2])
            msg_id = int(parts[3])
            attempt = int(parts[4]) if len(parts) > 4 else 1
            key = f"{chat_id}:{msg_id}"
            last_request_tuple = self.last_requests.get(key)
            if not last_request_tuple:
                await call.answer(self.strings["no_last_request"], show_alert=True)
                return
            last_parts, display_prompt = last_request_tuple
            use_url_context = bool(re.search(r'https?://\S+', display_prompt or ""))
            await call.edit(f"◴ <b>Обработка (попытка {attempt})...</b>", reply_markup=None)
            await self._send_to_gemini(
                message=msg_id,
                parts=last_parts,
                regeneration=False,
                call=call,
                chat_id_override=chat_id,
                use_url_context=use_url_context,
                display_prompt=display_prompt,
                attempt=attempt,
                is_retry=True,
            )
            return
        if action == "shreq":
            is_regen_flag = parts[2]
            chat_id = int(parts[3])
            msg_id = int(parts[4])
            attempt = int(parts[5]) if len(parts) > 5 else 1
            key = f"{chat_id}:{msg_id}"
            last_request_tuple = self.last_requests.get(key)
            if not last_request_tuple:
                await call.answer(self.strings["no_last_request"], show_alert=True)
                return
            _, display_prompt = last_request_tuple
            btn_action = "regen_att" if is_regen_flag == "1" else "retry"
            await call.edit(
                f"» <b>Ваш запрос:</b>\n<code>{utils.escape_html(display_prompt)}</code>",
                reply_markup=[[{"text": f"↺ Повторить ({attempt})", "data": f"gemini:{btn_action}:{chat_id}:{msg_id}:{attempt}"}]],
            )
            return

    @loader.watcher(only_incoming=True, ignore_edited=True)
    async def watcher(self, message: Message):
        if not hasattr(message, 'chat_id'): return
        cid = utils.get_chat_id(message)
        if cid not in self.impersonation_chats: return
        if message.is_private and not self.config["gauto_in_pm"]: return
        if message.out or (isinstance(message.from_id, tg_types.PeerUser) and message.from_id.user_id == self.me.id): return
        sender = await message.get_sender()
        if isinstance(sender, tg_types.User) and sender.bot: return
        if random.random() > self.config["impersonation_reply_chance"]: return
        parts, warnings = await self._prepare_parts(message)
        if warnings: logger.warning(f"Gauto warn: {warnings}")
        if not parts: return
        resp = await self._send_to_gemini(message=message, parts=parts, impersonation_mode=True)
        if resp and resp.strip():
            cln = resp.strip()
            await asyncio.sleep(random.uniform(2, 8))
            try: await self.client.send_read_acknowledge(cid, message=message)
            except: pass
            async with message.client.action(cid, "typing"):
                await asyncio.sleep(min(25.0, max(1.5, len(cln) * random.uniform(0.1, 0.25))))
            await message.reply(cln)

    async def _safe_del_msg(self, msg, delay=1):
        await asyncio.sleep(delay)
        try: await self.client.delete_messages(msg.chat_id, msg.id)
        except Exception as e: logger.warning(f"Ошибка удаления сообщения: {e}")