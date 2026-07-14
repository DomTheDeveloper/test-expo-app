import Mathlib
import Mathlib.Data.Nat.EvenOddRec

open Nat Finset

noncomputable def A005187 (e : ℕ) : ℕ :=
  Finset.sum (Finset.range (e + 1)) fun k ↦ e / (2^k)

noncomputable def A046644 (n : ℕ) : ℚ :=
  if n = 0 then 0
  else n.factorization.prod fun _ e ↦ (2 : ℚ) ^ (A005187 e)

noncomputable def A317940_f : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if n = 0 then 0
    else if n = 1 then 1
    else
      let A_n : ℚ := A046644 n
      let sum_of_products : ℚ := Finset.sum (divisors n) fun d ↦
        if h_prop : d > 1 ∧ d < n then
          have d_lt_n : d < n := h_prop.2
          let q := n / d
          have q_lt_n : q < n := Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) h_prop.1
          IH d d_lt_n * IH q q_lt_n
        else 0
      (A_n - sum_of_products) / 2

namespace A317940Verified

def ExactSpec : Prop := ∀ n : ℕ, n > 0 → A317940_f n ≥ 0

noncomputable def d : ℕ → ℚ :=
  Nat.evenOddRec (1 / 2)
    (fun r _ => 1 / (2 : ℚ) ^ (2 * r + 1))
    (fun r x => 2 * x - 1 / (2 : ℚ) ^ (2 * r + 2))

@[simp] theorem d_zero : d 0 = 1 / 2 := by
  simp [d]

@[simp] theorem d_even (r : ℕ) :
    d (2 * r) = 1 / (2 : ℚ) ^ (2 * r + 1) := by
  simp [d, Nat.evenOddRec_even]

@[simp] theorem d_odd (r : ℕ) :
    d (2 * r + 1) = 2 * d r - 1 / (2 : ℚ) ^ (2 * r + 2) := by
  simp [d, Nat.evenOddRec_odd]

theorem d_lower : ∀ n : ℕ, 1 / (2 : ℚ) ^ (n + 1) ≤ d n := by
  intro n
  induction n using Nat.evenOddRec with
  | h0 => norm_num [d]
  | h_even r ih =>
      simp [d_even]
  | h_odd r ih =>
      rw [d_odd]
      have hexp : r + 1 ≤ 2 * r + 2 := by omega
      have hbase :
          1 / (2 : ℚ) ^ (2 * r + 2) ≤ 1 / (2 : ℚ) ^ (r + 1) := by
        exact one_div_pow_le_one_div_pow_of_le (by norm_num) hexp
      have hle : 1 / (2 : ℚ) ^ (2 * r + 2) ≤ d r := hbase.trans ih
      linarith

theorem d_pos (n : ℕ) : 0 < d n := by
  have hpow : 0 < 1 / (2 : ℚ) ^ (n + 1) := by positivity
  exact lt_of_lt_of_le hpow (d_lower n)

noncomputable def a : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    match n with
    | 0 => 1
    | m + 1 =>
        Finset.sum (range (m + 1))
            (fun i => d i * IH (m - i) (Nat.lt_succ_of_le (Nat.sub_le m i))) /
          (2 * (m + 1))

@[simp] theorem a_zero : a 0 = 1 := by
  unfold a
  rw [WellFounded.fix_eq]

theorem a_succ (m : ℕ) :
    a (m + 1) =
      Finset.sum (range (m + 1)) (fun i => d i * a (m - i)) /
        (2 * (m + 1)) := by
  unfold a
  rw [WellFounded.fix_eq]
  rfl

theorem a_pos (n : ℕ) : 0 < a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ m =>
          rw [a_succ]
          have hnonneg :
              ∀ i ∈ range (m + 1), 0 ≤ d i * a (m - i) := by
            intro i hi
            exact mul_nonneg (le_of_lt (d_pos i))
              (le_of_lt (ih (m - i) (Nat.lt_succ_of_le (Nat.sub_le m i))))
          have hsum :
              0 < Finset.sum (range (m + 1)) (fun i => d i * a (m - i)) := by
            rw [sum_pos_iff_of_nonneg hnonneg]
            refine ⟨0, by simp, ?_⟩
            simpa using mul_pos (d_pos 0) (ih m (Nat.lt_succ_self m))
          have hden : 0 < (2 * (m + 1) : ℚ) := by positivity
          exact div_pos hsum hden

end A317940Verified
