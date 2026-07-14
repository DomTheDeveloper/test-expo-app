from pathlib import Path

path = Path("a317940/candidate.lean")
text = path.read_text()

replacements = [
    (
        "  rw [Finset.sum_range_succ']\n  congr 1\n",
        "  rw [Finset.sum_range_succ', add_comm]\n  congr 1\n",
    ),
    (
        "      rw [sum_range_even_odd_odd]\n",
        "      rw [show 2 * (m + 1) = 2 * m + 2 by omega, sum_range_even_odd_odd]\n",
    ),
    (
        "      | zero => norm_num [b, d]\n",
        "      | zero => simp [b_odd, d_zero, b_zero]\n",
    ),
    (
        "          rw [heven, hodd, geometric_shift, Finset.sum_sub_distrib]\n          have him := ih m (by omega)\n",
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
    ),
]

for old, new in replacements:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"Expected one occurrence, found {count}: {old!r}")
    text = text.replace(old, new)

Path("a317940/candidate.generated.lean").write_text(text)
print("Generated patched candidate:", len(text), "bytes")
