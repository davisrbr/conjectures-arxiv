from __future__ import annotations

import argparse
from collections import Counter
import math
from pathlib import Path
import sqlite3
import subprocess
import tempfile
from typing import Iterable


WIDTH = 1400
HEIGHT = 900
PNG_SCALE = 2
MARGIN_LEFT = 105
MARGIN_RIGHT = 40
MARGIN_TOP = 86
MARGIN_BOTTOM = 220
BAR_COLOR = "#2f6db5"
ACCENT_COLOR = "#c94f3d"
LINE_COLOR = "#7f8c9a"
GRID_COLOR = "#d6d9de"
TEXT_COLOR = "#1f2328"
BG_COLOR = "#ffffff"
MIN_CATEGORY_COUNT = 10

MATH_CATEGORY_NAMES = {
    "math.AC": "Commutative Algebra",
    "math.AG": "Algebraic Geometry",
    "math.AP": "Analysis of PDEs",
    "math.AT": "Algebraic Topology",
    "math.CA": "Classical Analysis and ODEs",
    "math.CO": "Combinatorics",
    "math.CT": "Category Theory",
    "math.CV": "Complex Variables",
    "math.DG": "Differential Geometry",
    "math.DS": "Dynamical Systems",
    "math.FA": "Functional Analysis",
    "math.GM": "General Mathematics",
    "math.GR": "Group Theory",
    "math.GT": "Geometric Topology",
    "math.KT": "K-Theory and Homology",
    "math.LO": "Logic",
    "math.MG": "Metric Geometry",
    "math.NA": "Numerical Analysis",
    "math.NT": "Number Theory",
    "math.OC": "Optimization and Control",
    "math.PR": "Probability",
    "math.QA": "Quantum Algebra",
    "math.RA": "Rings and Algebras",
    "math.RT": "Representation Theory",
    "math.SG": "Symplectic Geometry",
    "math.SP": "Spectral Theory",
    "math.ST": "Statistics Theory",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Create PNG histogram plots for labeled real conjectures.")
    parser.add_argument("--db-path", required=True)
    parser.add_argument("--model", default="gpt-5-mini")
    parser.add_argument("--output-dir", required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    conn = sqlite3.connect(args.db_path)
    try:
        rows = conn.execute(
            """
            SELECT
                p.primary_category,
                l.interestingness_score,
                l.viability_score
            FROM conjecture_llm_labels l
            JOIN conjectures c ON c.id = l.conjecture_id
            JOIN papers p ON p.arxiv_id = c.arxiv_id
            WHERE l.model = ?
              AND l.label = 'real_open_conjecture'
            ORDER BY c.id
            """,
            (args.model,),
        ).fetchall()
    finally:
        conn.close()

    if not rows:
        raise SystemExit(f"No real conjectures found for model={args.model}")

    categories = [str(row[0] or "(missing)") for row in rows if str(row[0] or "").startswith("math.")]
    interestingness = [float(row[1]) for row in rows]
    viability = [float(row[2]) for row in rows]

    category_counts = Counter(categories)
    category_items = sorted(
        ((MATH_CATEGORY_NAMES.get(code, code), count) for code, count in category_counts.items()),
        key=lambda item: (-item[1], item[0]),
    )

    write_plot_png(
        output_dir / "real_conjectures_primary_category_histogram.png",
        render_bar_chart(
            title="math.* arXiv Categories",
            subtitle="",
            items=category_items,
            x_label="Primary category",
            y_label="Conjecture count",
            rotate_labels=True,
        ),
    )
    write_plot_png(
        output_dir / "real_conjectures_interestingness_histogram.png",
        render_histogram(
            title="Interestingness Scores",
            subtitle="",
            values=interestingness,
            x_label="Interestingness score",
            y_label="Conjecture count",
        ),
    )
    write_plot_png(
        output_dir / "real_conjectures_viability_histogram.png",
        render_histogram(
            title="Viability Scores",
            subtitle="",
            values=viability,
            x_label="Viability score",
            y_label="Conjecture count",
        ),
    )
    write_plot_png(
        output_dir / "real_conjectures_category_mean_scores.png",
        render_category_score_panels(rows),
    )
    write_plot_png(
        output_dir / "real_conjectures_category_kde_scores.png",
        render_category_kde_panels(rows),
    )
    return 0


def render_bar_chart(
    *,
    title: str,
    subtitle: str,
    items: list[tuple[str, int]],
    x_label: str,
    y_label: str,
    rotate_labels: bool,
) -> str:
    max_value = max((value for _, value in items), default=1)
    y_ticks = tick_values(max_value)
    plot_height = HEIGHT - MARGIN_TOP - MARGIN_BOTTOM
    plot_width = WIDTH - MARGIN_LEFT - MARGIN_RIGHT
    bar_gap = 8
    bar_width = max(8.0, (plot_width - (len(items) - 1) * bar_gap) / max(len(items), 1))

    svg: list[str] = [svg_header()]
    svg.extend(background_and_titles(title=title, subtitle=subtitle))
    svg.extend(render_axes(y_ticks=y_ticks, x_label=x_label, y_label=y_label))

    for index, (label, value) in enumerate(items):
        x = MARGIN_LEFT + index * (bar_width + bar_gap)
        height = 0 if max_value == 0 else (value / max_value) * plot_height
        y = HEIGHT - MARGIN_BOTTOM - height
        svg.append(
            f'<rect x="{x:.1f}" y="{y:.1f}" width="{bar_width:.1f}" height="{height:.1f}" '
            f'fill="{BAR_COLOR}" rx="2" />'
        )
        svg.append(
            f'<text x="{x + bar_width / 2:.1f}" y="{y - 8:.1f}" text-anchor="middle" '
            f'font-size="15" fill="{TEXT_COLOR}">{value}</text>'
        )
        if rotate_labels:
            svg.append(
                f'<text transform="translate({x + bar_width / 2:.1f},{HEIGHT - MARGIN_BOTTOM + 26:.1f}) rotate(45)" '
                f'text-anchor="start" font-size="16" fill="{TEXT_COLOR}">{escape_xml(label)}</text>'
            )
        else:
            svg.append(
                f'<text x="{x + bar_width / 2:.1f}" y="{HEIGHT - MARGIN_BOTTOM + 32:.1f}" '
                f'text-anchor="middle" font-size="16" fill="{TEXT_COLOR}">{escape_xml(label)}</text>'
            )

    svg.append("</svg>")
    return "\n".join(svg)


def render_histogram(
    *,
    title: str,
    subtitle: str,
    values: list[float],
    x_label: str,
    y_label: str,
) -> str:
    bins = automatic_histogram_bins(values, minimum=0.0, maximum=1.0)
    return render_continuous_histogram(
        title=title,
        subtitle=subtitle,
        bins=bins,
        x_label=x_label,
        y_label=y_label,
    )


def render_category_score_panels(rows: list[tuple[str, float, float]]) -> str:
    grouped: dict[str, list[float]] = {}
    grouped_viability: dict[str, list[float]] = {}
    for category, interestingness, viability in rows:
        code = str(category or "")
        if not code.startswith("math."):
            continue
        grouped.setdefault(code, []).append(float(interestingness))
        grouped_viability.setdefault(code, []).append(float(viability))

    items = []
    for code, values in grouped.items():
        name = MATH_CATEGORY_NAMES.get(code, code)
        viability_values = grouped_viability[code]
        items.append(
            {
                "code": code,
                "label": name,
                "count": len(values),
                "interestingness_mean": sum(values) / len(values),
                "viability_mean": sum(viability_values) / len(viability_values),
            }
        )
    items = [item for item in items if int(item["count"]) >= MIN_CATEGORY_COUNT]
    interestingness_items = sorted(
        items,
        key=lambda item: (-float(item["interestingness_mean"]), -int(item["count"]), str(item["label"])),
    )
    viability_items = sorted(
        items,
        key=lambda item: (-float(item["viability_mean"]), -int(item["count"]), str(item["label"])),
    )

    row_height = 36
    panel_top = 150
    panel_bottom = 76
    panel_label_width = 290
    panel_inner_width = 410
    panel_gap = 80
    width = 1600
    height = panel_top + panel_bottom + row_height * max(len(interestingness_items), len(viability_items))
    left_panel_x = 70
    right_panel_x = left_panel_x + panel_label_width + panel_inner_width + panel_gap
    x_ticks = [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]

    svg: list[str] = [svg_open_tag(width, height)]
    svg.append(f'<rect width="{width}" height="{height}" fill="{BG_COLOR}" />')
    svg.append(
        f'<text x="{width / 2:.1f}" y="48" text-anchor="middle" font-size="34" font-weight="700" fill="{TEXT_COLOR}">Category-Level Scores</text>'
    )
    svg.append(
        f'<text x="{width / 2:.1f}" y="76" text-anchor="middle" font-size="19" fill="{TEXT_COLOR}">math.* primary categories with n ≥ {MIN_CATEGORY_COUNT}</text>'
    )

    svg.extend(
        render_horizontal_score_panel(
            origin_x=left_panel_x,
            top=panel_top,
            bottom=panel_bottom,
            label_width=panel_label_width,
            plot_width=panel_inner_width,
            total_height=height,
            title="Interestingness Mean",
            items=interestingness_items,
            value_key="interestingness_mean",
            bar_color=BAR_COLOR,
            x_ticks=x_ticks,
        )
    )
    svg.extend(
        render_horizontal_score_panel(
            origin_x=right_panel_x,
            top=panel_top,
            bottom=panel_bottom,
            label_width=panel_label_width,
            plot_width=panel_inner_width,
            total_height=height,
            title="Viability Mean",
            items=viability_items,
            value_key="viability_mean",
            bar_color=ACCENT_COLOR,
            x_ticks=x_ticks,
        )
    )

    svg.append("</svg>")
    return "\n".join(svg)


def render_category_kde_panels(rows: list[tuple[str, float, float]]) -> str:
    grouped: dict[str, dict[str, object]] = {}
    for category, interestingness, viability in rows:
        code = str(category or "")
        if not code.startswith("math."):
            continue
        entry = grouped.setdefault(
            code,
            {
                "label": MATH_CATEGORY_NAMES.get(code, code),
                "count": 0,
                "interestingness": [],
                "viability": [],
            },
        )
        entry["count"] = int(entry["count"]) + 1
        entry["interestingness"].append(float(interestingness))
        entry["viability"].append(float(viability))

    items = [item for item in grouped.values() if int(item["count"]) >= MIN_CATEGORY_COUNT]
    items.sort(key=lambda item: (-int(item["count"]), str(item["label"])))

    row_height = 42
    panel_top = 150
    panel_bottom = 76
    panel_label_width = 290
    panel_inner_width = 410
    panel_gap = 80
    width = 1600
    height = panel_top + panel_bottom + row_height * len(items)
    left_panel_x = 70
    right_panel_x = left_panel_x + panel_label_width + panel_inner_width + panel_gap
    x_ticks = [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]

    svg: list[str] = [svg_open_tag(width, height)]
    svg.append(f'<rect width="{width}" height="{height}" fill="{BG_COLOR}" />')
    svg.append(
        f'<text x="{width / 2:.1f}" y="48" text-anchor="middle" font-size="34" font-weight="700" fill="{TEXT_COLOR}">Score Distributions by arXiv Category</text>'
    )
    svg.append(
        f'<text x="{width / 2:.1f}" y="76" text-anchor="middle" font-size="19" fill="{TEXT_COLOR}">math.* primary categories with n ≥ {MIN_CATEGORY_COUNT}</text>'
    )

    svg.extend(
        render_kde_panel(
            origin_x=left_panel_x,
            top=panel_top,
            bottom=panel_bottom,
            label_width=panel_label_width,
            plot_width=panel_inner_width,
            total_height=height,
            title="Interestingness Distribution",
            items=items,
            values_key="interestingness",
            color=BAR_COLOR,
            x_ticks=x_ticks,
        )
    )
    svg.extend(
        render_kde_panel(
            origin_x=right_panel_x,
            top=panel_top,
            bottom=panel_bottom,
            label_width=panel_label_width,
            plot_width=panel_inner_width,
            total_height=height,
            title="Viability Distribution",
            items=items,
            values_key="viability",
            color=ACCENT_COLOR,
            x_ticks=x_ticks,
        )
    )

    svg.append("</svg>")
    return "\n".join(svg)


def render_horizontal_score_panel(
    *,
    origin_x: float,
    top: float,
    bottom: float,
    label_width: float,
    plot_width: float,
    total_height: float,
    title: str,
    items: list[dict[str, object]],
    value_key: str,
    bar_color: str,
    x_ticks: list[float],
) -> list[str]:
    row_height = 36
    label_x = origin_x + label_width - 12
    plot_x = origin_x + label_width
    plot_bottom = total_height - bottom
    plot_height = plot_bottom - top
    panel_right = plot_x + plot_width
    elements = [
        f'<text x="{origin_x + (label_width + plot_width) / 2:.1f}" y="{top - 24:.1f}" text-anchor="middle" font-size="24" font-weight="700" fill="{TEXT_COLOR}">{escape_xml(title)}</text>'
    ]

    for tick in x_ticks:
        x = plot_x + tick * plot_width
        elements.append(
            f'<line x1="{x:.1f}" y1="{top}" x2="{x:.1f}" y2="{plot_bottom}" stroke="{GRID_COLOR}" stroke-width="1" />'
        )
        elements.append(
            f'<text x="{x:.1f}" y="{plot_bottom + 26:.1f}" text-anchor="middle" font-size="16" fill="{TEXT_COLOR}">{tick:.1f}</text>'
        )
    elements.append(
        f'<line x1="{plot_x}" y1="{top}" x2="{plot_x}" y2="{plot_bottom}" stroke="{TEXT_COLOR}" stroke-width="2" />'
    )
    elements.append(
        f'<line x1="{plot_x}" y1="{plot_bottom}" x2="{panel_right}" y2="{plot_bottom}" stroke="{TEXT_COLOR}" stroke-width="2" />'
    )
    elements.append(
        f'<text x="{plot_x + plot_width / 2:.1f}" y="{total_height - 18:.1f}" text-anchor="middle" font-size="20" font-weight="600" fill="{TEXT_COLOR}">Mean score</text>'
    )

    for index, item in enumerate(items):
        y = top + 24 + index * row_height
        label = f"{item['label']} (n={item['count']})"
        value = float(item[value_key])
        bar_end = plot_x + value * plot_width

        if index % 2 == 0:
            elements.append(
                f'<rect x="{origin_x:.1f}" y="{y - 16:.1f}" width="{label_width + plot_width:.1f}" height="{row_height}" fill="#fafbfc" />'
            )
        elements.append(
            f'<text x="{label_x:.1f}" y="{y + 5:.1f}" text-anchor="end" font-size="17" fill="{TEXT_COLOR}">{escape_xml(label)}</text>'
        )
        elements.append(
            f'<rect x="{plot_x:.1f}" y="{y - 10:.1f}" width="{bar_end - plot_x:.1f}" height="20" fill="{bar_color}" rx="3" />'
        )
        elements.append(
            f'<text x="{bar_end + 8:.1f}" y="{y + 5:.1f}" text-anchor="start" font-size="16" fill="{TEXT_COLOR}">{value:.3f}</text>'
        )
    return elements


def render_kde_panel(
    *,
    origin_x: float,
    top: float,
    bottom: float,
    label_width: float,
    plot_width: float,
    total_height: float,
    title: str,
    items: list[dict[str, object]],
    values_key: str,
    color: str,
    x_ticks: list[float],
) -> list[str]:
    row_height = 42
    label_x = origin_x + label_width - 12
    plot_x = origin_x + label_width
    plot_bottom = total_height - bottom
    panel_right = plot_x + plot_width
    elements = [
        f'<text x="{origin_x + (label_width + plot_width) / 2:.1f}" y="{top - 24:.1f}" text-anchor="middle" font-size="24" font-weight="700" fill="{TEXT_COLOR}">{escape_xml(title)}</text>'
    ]

    for tick in x_ticks:
        x = plot_x + tick * plot_width
        elements.append(
            f'<line x1="{x:.1f}" y1="{top}" x2="{x:.1f}" y2="{plot_bottom}" stroke="{GRID_COLOR}" stroke-width="1" />'
        )
        elements.append(
            f'<text x="{x:.1f}" y="{plot_bottom + 26:.1f}" text-anchor="middle" font-size="16" fill="{TEXT_COLOR}">{tick:.1f}</text>'
        )
    elements.append(
        f'<line x1="{plot_x}" y1="{top}" x2="{plot_x}" y2="{plot_bottom}" stroke="{TEXT_COLOR}" stroke-width="2" />'
    )
    elements.append(
        f'<line x1="{plot_x}" y1="{plot_bottom}" x2="{panel_right}" y2="{plot_bottom}" stroke="{TEXT_COLOR}" stroke-width="2" />'
    )
    elements.append(
        f'<text x="{plot_x + plot_width / 2:.1f}" y="{total_height - 18:.1f}" text-anchor="middle" font-size="20" font-weight="600" fill="{TEXT_COLOR}">Score</text>'
    )

    for index, item in enumerate(items):
        y = top + 24 + index * row_height
        label = f"{item['label']} (n={item['count']})"
        values = [float(value) for value in item[values_key]]
        density_points = kde_points(values, num_points=120)
        max_density = max((density for _, density in density_points), default=1.0) or 1.0
        ridge_height = 24.0

        if index % 2 == 0:
            elements.append(
                f'<rect x="{origin_x:.1f}" y="{y - 18:.1f}" width="{label_width + plot_width:.1f}" height="{row_height}" fill="#fafbfc" />'
            )
        elements.append(
            f'<text x="{label_x:.1f}" y="{y + 5:.1f}" text-anchor="end" font-size="17" fill="{TEXT_COLOR}">{escape_xml(label)}</text>'
        )

        polygon_points = [f"{plot_x:.1f},{y:.1f}"]
        line_points: list[str] = []
        for x_value, density in density_points:
            x = plot_x + x_value * plot_width
            ridge_y = y - (density / max_density) * ridge_height
            polygon_points.append(f"{x:.1f},{ridge_y:.1f}")
            line_points.append(f"{x:.1f},{ridge_y:.1f}")
        polygon_points.append(f"{plot_x + plot_width:.1f},{y:.1f}")

        elements.append(
            f'<polygon points="{" ".join(polygon_points)}" fill="{color}" fill-opacity="0.28" stroke="none" />'
        )
        elements.append(
            f'<polyline points="{" ".join(line_points)}" fill="none" stroke="{color}" stroke-width="2.5" />'
        )

    return elements


def automatic_histogram_bins(
    values: Iterable[float],
    *,
    minimum: float,
    maximum: float,
) -> list[tuple[float, float, int]]:
    values = list(values)
    if not values:
        return [(minimum, maximum, 0)]

    sorted_values = sorted(min(max(value, minimum), maximum) for value in values)
    num_bins = automatic_bin_count(sorted_values, minimum=minimum, maximum=maximum)
    bin_width = (maximum - minimum) / num_bins
    counts = [0 for _ in range(num_bins)]
    for value in sorted_values:
        clipped = min(max(value, minimum), math.nextafter(maximum, minimum))
        index = min(int((clipped - minimum) / bin_width), num_bins - 1)
        counts[index] += 1

    bins = []
    for index, count in enumerate(counts):
        start = minimum + index * bin_width
        end = min(minimum + (index + 1) * bin_width, maximum)
        bins.append((start, end, count))
    return bins


def automatic_bin_count(values: list[float], *, minimum: float, maximum: float) -> int:
    n = len(values)
    if n <= 1:
        return 1

    q1 = quantile(values, 0.25)
    q3 = quantile(values, 0.75)
    iqr = max(q3 - q1, 0.0)
    if iqr > 0:
        bin_width = 2 * iqr * (n ** (-1 / 3))
        if bin_width > 0:
            raw_bins = math.ceil((maximum - minimum) / bin_width)
            return max(6, min(18, raw_bins))

    sturges_bins = math.ceil(math.log2(n) + 1)
    return max(6, min(18, sturges_bins))


def kde_points(values: list[float], *, num_points: int) -> list[tuple[float, float]]:
    if not values:
        return [(0.0, 0.0), (1.0, 0.0)]
    if len(values) == 1:
        return [(index / (num_points - 1), 0.0 if index != num_points // 2 else 1.0) for index in range(num_points)]

    bandwidth = kde_bandwidth(values)
    points = []
    norm = 1 / math.sqrt(2 * math.pi)
    for index in range(num_points):
        x = index / (num_points - 1)
        density = 0.0
        for value in values:
            z = (x - value) / bandwidth
            density += math.exp(-0.5 * z * z)
        density *= norm / (len(values) * bandwidth)
        points.append((x, density))
    return points


def kde_bandwidth(values: list[float]) -> float:
    n = len(values)
    mean = sum(values) / n
    variance = sum((value - mean) ** 2 for value in values) / max(n - 1, 1)
    std = math.sqrt(variance)
    q1 = quantile(sorted(values), 0.25)
    q3 = quantile(sorted(values), 0.75)
    iqr = max(q3 - q1, 0.0)
    scale = min(std, iqr / 1.34) if std > 0 and iqr > 0 else max(std, iqr / 1.34)
    if scale <= 0:
        scale = 0.12
    bandwidth = 0.9 * scale * (n ** (-1 / 5))
    return min(max(bandwidth, 0.04), 0.16)


def quantile(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    if len(values) == 1:
        return values[0]
    position = (len(values) - 1) * probability
    lower = int(math.floor(position))
    upper = int(math.ceil(position))
    if lower == upper:
        return values[lower]
    weight = position - lower
    return values[lower] * (1 - weight) + values[upper] * weight


def render_continuous_histogram(
    *,
    title: str,
    subtitle: str,
    bins: list[tuple[float, float, int]],
    x_label: str,
    y_label: str,
) -> str:
    max_value = max((count for _, _, count in bins), default=1)
    y_ticks = tick_values(max_value)
    plot_height = HEIGHT - MARGIN_TOP - MARGIN_BOTTOM
    plot_width = WIDTH - MARGIN_LEFT - MARGIN_RIGHT
    plot_bottom = HEIGHT - MARGIN_BOTTOM
    plot_right = WIDTH - MARGIN_RIGHT
    x_ticks = [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]

    svg: list[str] = [svg_header()]
    svg.extend(background_and_titles(title=title, subtitle=subtitle))
    svg.append(
        f'<line x1="{MARGIN_LEFT}" y1="{MARGIN_TOP}" x2="{MARGIN_LEFT}" y2="{plot_bottom}" stroke="{TEXT_COLOR}" stroke-width="2" />'
    )
    svg.append(
        f'<line x1="{MARGIN_LEFT}" y1="{plot_bottom}" x2="{plot_right}" y2="{plot_bottom}" stroke="{TEXT_COLOR}" stroke-width="2" />'
    )
    svg.append(
        f'<text x="{(MARGIN_LEFT + plot_right) / 2:.1f}" y="{HEIGHT - 36}" text-anchor="middle" font-size="22" font-weight="600" fill="{TEXT_COLOR}">{escape_xml(x_label)}</text>'
    )
    svg.append(
        f'<text transform="translate(34,{MARGIN_TOP + plot_height / 2:.1f}) rotate(-90)" text-anchor="middle" font-size="22" font-weight="600" fill="{TEXT_COLOR}">{escape_xml(y_label)}</text>'
    )

    for tick in y_ticks:
        y = plot_bottom - (tick / max(y_ticks)) * plot_height
        svg.append(
            f'<line x1="{MARGIN_LEFT}" y1="{y:.1f}" x2="{plot_right}" y2="{y:.1f}" stroke="{GRID_COLOR}" stroke-width="1" />'
        )
        svg.append(
            f'<text x="{MARGIN_LEFT - 12}" y="{y + 6:.1f}" text-anchor="end" font-size="16" fill="{TEXT_COLOR}">{tick}</text>'
        )

    for tick in x_ticks:
        x = MARGIN_LEFT + tick * plot_width
        svg.append(
            f'<line x1="{x:.1f}" y1="{MARGIN_TOP}" x2="{x:.1f}" y2="{plot_bottom}" stroke="{GRID_COLOR}" stroke-width="1" />'
        )
        svg.append(
            f'<text x="{x:.1f}" y="{plot_bottom + 26:.1f}" text-anchor="middle" font-size="16" fill="{TEXT_COLOR}">{tick:.1f}</text>'
        )

    for start, end, count in bins:
        x0 = MARGIN_LEFT + start * plot_width
        x1 = MARGIN_LEFT + end * plot_width
        bar_width = max(x1 - x0 - 2, 1)
        height = 0 if max_value == 0 else (count / max_value) * plot_height
        y = plot_bottom - height
        svg.append(
            f'<rect x="{x0 + 1:.1f}" y="{y:.1f}" width="{bar_width:.1f}" height="{height:.1f}" fill="{BAR_COLOR}" rx="1.5" />'
        )

    svg.append("</svg>")
    return "\n".join(svg)


def background_and_titles(*, title: str, subtitle: str) -> list[str]:
    items = [
        f'<rect width="{WIDTH}" height="{HEIGHT}" fill="{BG_COLOR}" />',
        f'<text x="{WIDTH / 2:.1f}" y="48" text-anchor="middle" font-size="34" font-weight="700" fill="{TEXT_COLOR}">{escape_xml(title)}</text>',
    ]
    if subtitle:
        items.append(
            f'<text x="{WIDTH / 2:.1f}" y="76" text-anchor="middle" font-size="19" fill="{TEXT_COLOR}">{escape_xml(subtitle)}</text>'
        )
    return items


def render_axes(*, y_ticks: list[int], x_label: str, y_label: str) -> list[str]:
    plot_bottom = HEIGHT - MARGIN_BOTTOM
    plot_right = WIDTH - MARGIN_RIGHT
    plot_height = HEIGHT - MARGIN_TOP - MARGIN_BOTTOM
    max_tick = max(y_ticks) if y_ticks else 1
    svg = [
        f'<line x1="{MARGIN_LEFT}" y1="{MARGIN_TOP}" x2="{MARGIN_LEFT}" y2="{plot_bottom}" stroke="{TEXT_COLOR}" stroke-width="2" />',
        f'<line x1="{MARGIN_LEFT}" y1="{plot_bottom}" x2="{plot_right}" y2="{plot_bottom}" stroke="{TEXT_COLOR}" stroke-width="2" />',
        f'<text x="{(MARGIN_LEFT + plot_right) / 2:.1f}" y="{HEIGHT - 36}" text-anchor="middle" font-size="22" font-weight="600" fill="{TEXT_COLOR}">{escape_xml(x_label)}</text>',
        f'<text transform="translate(34,{MARGIN_TOP + plot_height / 2:.1f}) rotate(-90)" text-anchor="middle" font-size="22" font-weight="600" fill="{TEXT_COLOR}">{escape_xml(y_label)}</text>',
    ]

    for tick in y_ticks:
        y = plot_bottom - (tick / max_tick) * plot_height
        svg.append(
            f'<line x1="{MARGIN_LEFT}" y1="{y:.1f}" x2="{plot_right}" y2="{y:.1f}" stroke="{GRID_COLOR}" stroke-width="1" />'
        )
        svg.append(
            f'<text x="{MARGIN_LEFT - 12}" y="{y + 6:.1f}" text-anchor="end" font-size="16" fill="{TEXT_COLOR}">{tick}</text>'
        )
    return svg


def tick_values(max_value: int) -> list[int]:
    if max_value <= 5:
        return list(range(0, max_value + 1))
    magnitude = 10 ** max(0, int(math.log10(max_value)) - 1)
    candidates = [1, 2, 5, 10]
    step = magnitude
    for candidate in candidates:
        candidate_step = candidate * magnitude
        if max_value / candidate_step <= 8:
            step = candidate_step
            break
    top = int(math.ceil(max_value / step) * step)
    return list(range(0, top + step, step))


def svg_open_tag(width: int, height: int) -> str:
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width * PNG_SCALE}" height="{height * PNG_SCALE}" '
        f'viewBox="0 0 {width} {height}">'
    )


def svg_header() -> str:
    return svg_open_tag(WIDTH, HEIGHT)


def write_plot_png(path: Path, content: str) -> None:
    with tempfile.NamedTemporaryFile("w", suffix=".svg", delete=False, encoding="utf-8") as handle:
        handle.write(content + "\n")
        temp_svg = Path(handle.name)
    try:
        subprocess.run(
            ["magick", str(temp_svg), f"PNG24:{path}"],
            check=True,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError as exc:
        raise RuntimeError("ImageMagick `magick` is required to render PNG plots.") from exc
    finally:
        temp_svg.unlink(missing_ok=True)


def escape_xml(value: str) -> str:
    return (
        value.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
        .replace("'", "&apos;")
    )


if __name__ == "__main__":
    raise SystemExit(main())
