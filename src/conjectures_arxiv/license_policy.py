from __future__ import annotations

from dataclasses import dataclass
import re
from urllib.parse import urlsplit, urlunsplit


PUBLICATION_POLICY_VERSION = "hf-publication-v2"

_TRAILING_LICENSE_SUFFIX = re.compile(r"/(?:legalcode|deed(?:\.[a-z0-9_-]+)?)$", flags=re.IGNORECASE)


@dataclass(frozen=True)
class LicenseDecision:
    raw_license_url: str
    normalized_license_url: str
    license_family: str
    decision: str
    can_publish_text: bool
    reason: str
    policy_version: str = PUBLICATION_POLICY_VERSION


def classify_license_for_publication(license_url: str) -> LicenseDecision:
    raw_license_url = license_url.strip()
    normalized_license_url = normalize_license_url(raw_license_url)
    host, path_parts = _split_license_url(normalized_license_url)

    if not normalized_license_url:
        return LicenseDecision(
            raw_license_url=raw_license_url,
            normalized_license_url="",
            license_family="missing",
            decision="publish_text",
            can_publish_text=True,
            reason="missing_license_treated_as_publishable",
        )

    if host.endswith("arxiv.org") and "nonexclusive-distrib" in path_parts:
        return LicenseDecision(
            raw_license_url=raw_license_url,
            normalized_license_url=normalized_license_url,
            license_family="arxiv_nonexclusive_distrib",
            decision="withhold_text",
            can_publish_text=False,
            reason="arxiv_nonexclusive_distribution_license",
        )

    if host.endswith("creativecommons.org"):
        family = _classify_creative_commons_family(path_parts)
        if family != "unknown":
            reason = "creativecommons_license_treated_as_publishable"
            if family in {"cc_by_nc", "cc_by_nc_sa", "cc_by_nc_nd"}:
                reason = "creativecommons_noncommercial_license_allowed_for_noncommercial_release"
            return LicenseDecision(
                raw_license_url=raw_license_url,
                normalized_license_url=normalized_license_url,
                license_family=family,
                decision="publish_text",
                can_publish_text=True,
                reason=reason,
            )

    if _looks_like_all_rights_reserved(normalized_license_url):
        return LicenseDecision(
            raw_license_url=raw_license_url,
            normalized_license_url=normalized_license_url,
            license_family="all_rights_reserved",
            decision="withhold_text",
            can_publish_text=False,
            reason="all_rights_reserved_license",
        )

    return LicenseDecision(
        raw_license_url=raw_license_url,
        normalized_license_url=normalized_license_url,
        license_family="unknown",
        decision="publish_text",
        can_publish_text=True,
        reason="unrecognized_license_treated_as_publishable",
    )


def normalize_license_url(license_url: str) -> str:
    cleaned = license_url.strip()
    if not cleaned:
        return ""

    parsed = urlsplit(cleaned)
    host = parsed.netloc.lower()
    if host.startswith("www."):
        host = host[4:]

    path = parsed.path.strip()
    if not path and not host and not parsed.scheme:
        return cleaned.lower()

    normalized_path = path.rstrip("/")
    normalized_path = _TRAILING_LICENSE_SUFFIX.sub("", normalized_path)
    if normalized_path:
        normalized_path = normalized_path.lower() + "/"

    scheme = "https" if host in {"creativecommons.org", "arxiv.org"} else (parsed.scheme.lower() or "https")
    return urlunsplit((scheme, host, normalized_path, "", ""))


def publication_metadata_from_license(license_url: str) -> dict[str, object]:
    decision = classify_license_for_publication(license_url)
    return {
        "normalized_license_url": decision.normalized_license_url,
        "license_family": decision.license_family,
        "publication_decision": decision.decision,
        "publication_text_allowed": decision.can_publish_text,
        "publication_text_reason": decision.reason,
        "publication_policy_version": decision.policy_version,
    }


def _classify_creative_commons_family(path_parts: list[str]) -> str:
    if len(path_parts) >= 3 and path_parts[0] == "publicdomain" and path_parts[1] == "zero":
        return "cc0"

    if len(path_parts) < 2 or path_parts[0] != "licenses":
        return "unknown"

    code = path_parts[1]
    return {
        "by": "cc_by",
        "by-sa": "cc_by_sa",
        "by-nd": "cc_by_nd",
        "by-nc": "cc_by_nc",
        "by-nc-sa": "cc_by_nc_sa",
        "by-nc-nd": "cc_by_nc_nd",
    }.get(code, "unknown")


def _looks_like_all_rights_reserved(license_url: str) -> bool:
    lowered = license_url.lower()
    return "all-rights-reserved" in lowered or "rightsstatements.org/vocab/inc/" in lowered


def _split_license_url(license_url: str) -> tuple[str, list[str]]:
    if not license_url:
        return "", []
    parsed = urlsplit(license_url)
    host = parsed.netloc.lower()
    path_parts = [part for part in parsed.path.lower().split("/") if part]
    return host, path_parts
