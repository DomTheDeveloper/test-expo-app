from pathlib import Path

path = Path("a317940/candidate.lean")
text = path.read_text()


def replace_exact(old: str, new: str, expected: int = 1) -> None:
    global text
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"Expected {expected} occurrences, found {count}: {old!r}")
    text = text.replace(old, new)


replace_exact(
    "  rw [Finset.sum_range_succ']\n"
    "  congr 1\n"
    "  · norm_num\n"
    "  · apply Finset.sum_congr rfl\n"
    "    intro r hr\n"
    "    rw [show 2 * (r + 1) + 1 = 2 * r + 3 by omega,\n"
    "      show m - (r + 1) = m - r - 1 by omega]\n",
    "  rw [Finset.sum_range_succ', add_comm]\n"
    "  congr 1\n"
    "  ring\n",
)

replace_exact(
    "      rw [sum_range_even_odd_odd]\n",
    "      rw [show 2 * (m + 1) = 2 * m + 2 by omega, sum_range_even_odd_odd]\n",
)

replace_exact(
    "      | zero => norm_num [b, d]\n",
    "      | zero =>\n"
    "          have hb1 : b 1 = 1 / 2 := by simpa using b_odd 0\n"
    "          norm_num [hb1, d_zero, b_zero]\n",
)

replace_exact(
    "          rw [heven, hodd, geometric_shift, Finset.sum_sub_distrib]\n"
    "          have him := ih m (by omega)\n",
    "          rw [heven, hodd, geometric_shift, Finset.sum_sub_distrib]\n"
    "          have hshift :\n"
    "              Finset.sum (range (m + 1))\n"
    "                  (fun r => 1 / (2 : ℚ) ^ (2 * r + 3) * b (m + 1 - r - 1)) =\n"
    "                Finset.sum (range (m + 1))\n"
    "                  (fun r => 1 / (2 : ℚ) ^ (2 * r + 3) * b (m - r)) := by\n"
    "            apply Finset.sum_congr rfl\n"
    "            intro r hr\n"
    "            rw [show m + 1 - r - 1 = m - r by omega]\n"
    "          rw [hshift]\n"
    "          have him := ih m (by omega)\n",
)

replace_exact(
    "      rw [← him]\n      ring\n",
    "      rw [← him]\n      ring_nf\n",
)

replace_exact(
    "          rw [← him]\n          ring\n",
    "          rw [← him]\n          ring_nf\n",
)

Path("a317940/candidate.generated.lean").write_text(text)
print("Generated patched candidate:", len(text), "bytes")
