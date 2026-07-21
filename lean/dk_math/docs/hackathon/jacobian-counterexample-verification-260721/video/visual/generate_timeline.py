#!/usr/bin/env python3
"""Generate measured visual timing, ASS cards, and SRT subtitles."""

from __future__ import annotations

import csv
import json
import re
import sys
from pathlib import Path


CARDS = {
    "01": (
        "A candidate counterexample was reported.",
        "Reported is not yet verified.",
        "Breaking Math Verification",
    ),
    "02": (
        "From report to certificate",
        "reported claim  →  independent reconstruction  →  explicit witness",
        "Lean certificate  →  axiom audit",
    ),
    "03": (
        "The exact polynomial map",
        "F = (P, Q, R)",
        "P = (1 + xy)³z + y²(1 + xy)(4 + 3xy)\n"
        "Q = y + 3x(1 + xy)²z + 3xy²(4 + 3xy)\n"
        "R = 2x − 3x²y − x³z",
    ),
    "04": (
        "Formal Jacobian · exact normalization",
        "det J(F) = −2    →    F̃ = (−P/2, Q, R)",
        "det J(F̃) = 1",
    ),
    "05": (
        "Three distinct inputs · one exact target",
        "p₀ ≠ p₁     p₀ ≠ p₂     p₁ ≠ p₂",
        "F̃(p₀) = F̃(p₁) = F̃(p₂) = (1/8, 0, 0)",
    ),
    "06": (
        "A reusable collision certificate",
        "DkMath.Verification.CollisionCertificate",
        "normalizedCollisionCertificateC_notInjective\n"
        "normalizedCollisionCertificateC_noLeftInverse",
    ),
    "07": (
        "The compiled Lean surface",
        "normalizedJacobianCounterexampleCertificateC\n"
        "normalized_three_point_collision_C\n"
        "normalizedCollisionCertificateC_notInjective",
        "Jacobian certificate: propext · Classical.choice · Quot.sound\n"
        "generic collision consequence: no axioms",
    ),
    "08": (
        "Two AI workflows · one auditable handoff",
        "GPT-5.6  →  Git repository  →  Codex  →  Lean kernel",
        "BMV-001 architecture · BMV-002 certificate · BMV-003 adapter\n"
        "BMV-004 contracts · BMV-005 cross-domain validation · BMV-006 public API",
    ),
    "09": (
        "Honest scope",
        "Lean verifies the exact formalized formulas.",
        "It does not certify:\n"
        "historical priority · publication status · peer review · community acceptance",
    ),
    "10": (
        "Breaking Math Verification",
        "GPT-5.6 × Codex × Lean 4",
        "Do not trust the headline.  Verify the certificate.",
    ),
}


def ass_time(seconds: float) -> str:
    centis = round(seconds * 100)
    hours, rem = divmod(centis, 360000)
    minutes, rem = divmod(rem, 6000)
    secs, cs = divmod(rem, 100)
    return f"{hours}:{minutes:02d}:{secs:02d}.{cs:02d}"


def srt_time(seconds: float) -> str:
    millis = round(seconds * 1000)
    hours, rem = divmod(millis, 3_600_000)
    minutes, rem = divmod(rem, 60_000)
    secs, ms = divmod(rem, 1000)
    return f"{hours:02d}:{minutes:02d}:{secs:02d},{ms:03d}"


def ass_text(text: str) -> str:
    return text.replace("\n", r"\N")


def main() -> None:
    timing_path = Path(sys.argv[1])
    tts_dir = Path(sys.argv[2])
    ass_path = Path(sys.argv[3])
    srt_path = Path(sys.argv[4])
    json_path = Path(sys.argv[5])

    with timing_path.open(encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))

    timeline = []
    for row in rows:
        cue = row["cue"]
        text = (tts_dir / row["text_file"]).read_text(encoding="utf-8").strip()
        timeline.append(
            {
                "cue": cue,
                "start": float(row["start"]),
                "end": float(row["end"]),
                "raw_seconds": float(row["raw_seconds"]),
                "slot_seconds": float(row["slot_seconds"]),
                "atempo": float(row["atempo"]),
                "text": text,
            }
        )

    header = """[Script Info]
ScriptType: v4.00+
PlayResX: 1280
PlayResY: 720
ScaledBorderAndShadow: yes

[V4+ Styles]
Format: Name, Fontname, Fontsize, PrimaryColour, SecondaryColour, OutlineColour, BackColour, Bold, Italic, Underline, StrikeOut, ScaleX, ScaleY, Spacing, Angle, BorderStyle, Outline, Shadow, Alignment, MarginL, MarginR, MarginV, Encoding
Style: Title,DejaVu Sans,46,&H00F8FAFC,&H000000FF,&H0008111F,&H00000000,-1,0,0,0,100,100,0,0,1,2,0,8,70,70,65,1
Style: Body,DejaVu Sans,31,&H00F8FAFC,&H000000FF,&H0008111F,&H00000000,0,0,0,0,100,100,0,0,1,1,0,5,80,80,35,1
Style: Code,DejaVu Sans Mono,25,&H00F9E267,&H000000FF,&H0008111F,&H00000000,0,0,0,0,100,100,0,0,1,1,0,5,70,70,30,1
Style: Accent,DejaVu Sans,38,&H00C4A7FF,&H000000FF,&H0008111F,&H00000000,-1,0,0,0,100,100,0,0,1,2,0,5,50,50,30,1
Style: Node,DejaVu Sans,34,&H00F8FAFC,&H000000FF,&H00E29D67,&H00000000,-1,0,0,0,100,100,0,0,1,3,0,5,20,20,20,1

[Events]
Format: Layer, Start, End, Style, Name, MarginL, MarginR, MarginV, Effect, Text
"""
    events = []
    for item in timeline:
        cue = item["cue"]
        start = ass_time(item["start"])
        end = ass_time(item["end"])
        title, body, code = CARDS[cue]
        events.append(f"Dialogue: 0,{start},{end},Title,,0,0,0,,{ass_text(title)}")
        events.append(
            f"Dialogue: 0,{start},{end},Body,,0,0,0,,"
            f"{{\\pos(640,265)}}{ass_text(body)}"
        )
        events.append(
            f"Dialogue: 0,{start},{end},Code,,0,0,0,,"
            f"{{\\pos(640,415)}}{ass_text(code)}"
        )
        if cue == "04":
            events.append(
                f"Dialogue: 1,{start},{end},Accent,,0,0,0,,"
                "{\\pos(640,520)\\fad(900,500)}formal determinant = 1"
            )
        if cue == "05":
            duration_ms = round((item["end"] - item["start"]) * 1000)
            move_end = min(duration_ms - 800, 6500)
            events.extend(
                [
                    f"Dialogue: 2,{start},{end},Node,,0,0,0,,"
                    f"{{\\move(220,310,520,405,800,{move_end})}}p₀",
                    f"Dialogue: 2,{start},{end},Node,,0,0,0,,"
                    f"{{\\move(220,405,520,405,1100,{move_end})}}p₁",
                    f"Dialogue: 2,{start},{end},Node,,0,0,0,,"
                    f"{{\\move(220,500,520,405,1400,{move_end})}}p₂",
                    f"Dialogue: 2,{start},{end},Accent,,0,0,0,,"
                    "{\\pos(815,405)\\fad(700,400)}(1/8, 0, 0)",
                ]
            )

    ass_path.write_text(header + "\n".join(events) + "\n", encoding="utf-8")

    srt_blocks = []
    subtitle_index = 1
    for item in timeline:
        sentences = [
            sentence.strip()
            for sentence in re.split(r"(?<=[.!?])\s+", item["text"])
            if sentence.strip()
        ]
        weights = [max(len(sentence), 1) for sentence in sentences]
        spoken_end = min(item["start"] + item["raw_seconds"], item["end"] - 0.1)
        spoken_span = spoken_end - item["start"]
        cursor = item["start"]
        for sentence, weight in zip(sentences, weights):
            duration = spoken_span * weight / sum(weights)
            sentence_end = min(cursor + duration, spoken_end)
            srt_blocks.append(
                f"{subtitle_index}\n{srt_time(cursor)} --> {srt_time(sentence_end)}\n"
                f"{sentence}\n"
            )
            subtitle_index += 1
            cursor = sentence_end
    srt_path.write_text("\n".join(srt_blocks), encoding="utf-8")
    json_path.write_text(json.dumps(timeline, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
