from conjectures_arxiv.license_policy import classify_license_for_publication


def test_missing_license_defaults_to_publishable() -> None:
    decision = classify_license_for_publication("")

    assert decision.can_publish_text is True
    assert decision.decision == "publish_text"
    assert decision.license_family == "missing"
    assert decision.reason == "missing_license_treated_as_publishable"


def test_noncommercial_license_is_publishable_for_noncommercial_release() -> None:
    decision = classify_license_for_publication("http://creativecommons.org/licenses/by-nc-sa/4.0/legalcode")

    assert decision.can_publish_text is True
    assert decision.decision == "publish_text"
    assert decision.license_family == "cc_by_nc_sa"
    assert decision.reason == "creativecommons_noncommercial_license_allowed_for_noncommercial_release"
    assert decision.normalized_license_url == "https://creativecommons.org/licenses/by-nc-sa/4.0/"


def test_noncommercial_no_derivatives_license_is_publishable_for_noncommercial_release() -> None:
    decision = classify_license_for_publication("https://creativecommons.org/licenses/by-nc-nd/4.0/deed.en")

    assert decision.can_publish_text is True
    assert decision.decision == "publish_text"
    assert decision.license_family == "cc_by_nc_nd"
    assert decision.reason == "creativecommons_noncommercial_license_allowed_for_noncommercial_release"
    assert decision.normalized_license_url == "https://creativecommons.org/licenses/by-nc-nd/4.0/"


def test_arxiv_nonexclusive_license_withholds_text() -> None:
    decision = classify_license_for_publication("http://arxiv.org/licenses/nonexclusive-distrib/1.0/")

    assert decision.can_publish_text is False
    assert decision.decision == "withhold_text"
    assert decision.license_family == "arxiv_nonexclusive_distrib"
    assert decision.reason == "arxiv_nonexclusive_distribution_license"
    assert decision.normalized_license_url == "https://arxiv.org/licenses/nonexclusive-distrib/1.0/"


def test_open_creative_commons_license_stays_publishable() -> None:
    decision = classify_license_for_publication("https://creativecommons.org/licenses/by-sa/4.0/deed.en")

    assert decision.can_publish_text is True
    assert decision.decision == "publish_text"
    assert decision.license_family == "cc_by_sa"
    assert decision.reason == "creativecommons_license_treated_as_publishable"
    assert decision.normalized_license_url == "https://creativecommons.org/licenses/by-sa/4.0/"


def test_unknown_license_defaults_to_publishable() -> None:
    decision = classify_license_for_publication("https://example.org/custom-license")

    assert decision.can_publish_text is True
    assert decision.decision == "publish_text"
    assert decision.license_family == "unknown"
    assert decision.reason == "unrecognized_license_treated_as_publishable"
