import WOWII.ZZGraphConjecture314C5Embedding

/-!
An induced five-cycle dominates a connected triangle-free induced-`P₅`-free
graph. This is the first half of the nonbipartite classification for WOWII 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private lemma cycle_step_adj
    {G : SimpleGraph α} {c : Fin 5 → α}
    (hc : IsInducedC5Embedding G c) (i : Fin 5) :
    G.Adj (c i) (c (i + 1)) :=
  (hc.2 i (i + 1)).mpr (by simp [cycleGraph_adj])

private lemma cycle_back_step_adj
    {G : SimpleGraph α} {c : Fin 5 → α}
    (hc : IsInducedC5Embedding G c) (i : Fin 5) :
    G.Adj (c i) (c (i - 1)) :=
  (hc.2 i (i - 1)).mpr (by simp [cycleGraph_adj])

private lemma cycle_two_step_not_adj
    {G : SimpleGraph α} {c : Fin 5 → α}
    (hc : IsInducedC5Embedding G c) (i : Fin 5) :
    ¬G.Adj (c i) (c (i + 2)) := by
  rw [hc.2]
  fin_cases i <;> decide

private lemma cycle_back_two_step_not_adj
    {G : SimpleGraph α} {c : Fin 5 → α}
    (hc : IsInducedC5Embedding G c) (i : Fin 5) :
    ¬G.Adj (c i) (c (i - 2)) := by
  rw [hc.2]
  fin_cases i <;> decide

/-- Every vertex has a neighbor on an induced five-cycle under the exact
triangle-free and induced-`P₅`-free hypotheses. -/
lemma exists_adj_cycleVertex_of_inducedC5
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    (c : Fin 5 → α) (hc : IsInducedC5Embedding G c)
    (x : α) :
    ∃ i : Fin 5, G.Adj x (c i) := by
  by_contra hnone
  push_neg at hnone
  obtain ⟨i, hi⟩ := Finite.exists_min (fun j : Fin 5 => G.dist x (c j))
  have hle3 : G.dist x (c i) ≤ 3 :=
    dist_le_three_of_no_FormsInducedP5 G hG hNoP5 x (c i)
  have hne0 : G.dist x (c i) ≠ 0 := by
    intro h0
    have hxi : x = c i := (hG.dist_eq_zero_iff).mp h0
    have hed := cycle_step_adj hc i
    exact hnone (i + 1) (hxi ▸ hed)
  have hne1 : G.dist x (c i) ≠ 1 := by
    intro h1
    exact hnone i (dist_eq_one_iff_adj.mp h1)
  have hd : G.dist x (c i) = 2 ∨ G.dist x (c i) = 3 := by omega
  rcases hd with hd2 | hd3
  · obtain ⟨p, hp, hpgeo⟩ := hG.exists_path_of_dist x (c i)
    have hplen : p.length = 2 := hpgeo.trans hd2
    let a := p.getVert 1
    have hxa : G.Adj x a := by
      simpa [a] using p.adj_getVert_succ (i := 0) (by omega)
    have hai : G.Adj a (c i) := by
      have h := p.adj_getVert_succ (i := 1) (by omega)
      have hend : p.getVert 2 = c i := by simpa [hplen] using p.getVert_length
      simpa [a, hend] using h
    have ha_next : ¬G.Adj a (c (i + 1)) := by
      intro h
      exact hTriFree a (c i) (c (i + 1)) hai (cycle_step_adj hc i) h.symm
    have ha_prev : ¬G.Adj a (c (i - 1)) := by
      intro h
      exact hTriFree a (c i) (c (i - 1)) hai (cycle_back_step_adj hc i) h.symm
    have hx_cycle : ∀ j : Fin 5, ¬G.Adj x (c j) := hnone
    by_cases ha2 : G.Adj a (c (i + 2))
    · have hbackPair : G.Adj (c (i - 2)) (c (i + 2)) := by
        apply (hc.2 (i - 2) (i + 2)).mpr
        fin_cases i <;> decide
      have haBack2 : ¬G.Adj a (c (i - 2)) := by
        intro h
        exact hTriFree a (c (i + 2)) (c (i - 2)) ha2 hbackPair.symm h.symm
      apply hNoP5 x a (c i) (c (i - 1)) (c (i - 2))
      unfold FormsInducedP5
      have hci1 := cycle_back_step_adj hc i
      have hci2 := cycle_back_step_adj hc (i - 1)
      exact ⟨hxa.ne, (hx_cycle i).ne, (hx_cycle (i - 1)).ne,
        (hx_cycle (i - 2)).ne,
        hai.ne, ha_prev.ne, haBack2.ne,
        hci1.ne, (cycle_back_two_step_not_adj hc i).ne,
        hci2.ne,
        hxa, hai, hci1, hci2,
        hx_cycle i, hx_cycle (i - 1), hx_cycle (i - 2),
        ha_prev, haBack2, cycle_back_two_step_not_adj hc i⟩
    · apply hNoP5 x a (c i) (c (i + 1)) (c (i + 2))
      unfold FormsInducedP5
      have hci1 := cycle_step_adj hc i
      have hci2 := cycle_step_adj hc (i + 1)
      exact ⟨hxa.ne, (hx_cycle i).ne, (hx_cycle (i + 1)).ne,
        (hx_cycle (i + 2)).ne,
        hai.ne, ha_next.ne, ha2.ne,
        hci1.ne, (cycle_two_step_not_adj hc i).ne,
        hci2.ne,
        hxa, hai, hci1, hci2,
        hx_cycle i, hx_cycle (i + 1), hx_cycle (i + 2),
        ha_next, ha2, cycle_two_step_not_adj hc i⟩
  · obtain ⟨p, hp, hpgeo⟩ := hG.exists_path_of_dist x (c i)
    have hplen : p.length = 3 := hpgeo.trans hd3
    let a := p.getVert 1
    let b := p.getVert 2
    have hxa : G.Adj x a := by
      simpa [a] using p.adj_getVert_succ (i := 0) (by omega)
    have hab : G.Adj a b := by
      simpa [a, b] using p.adj_getVert_succ (i := 1) (by omega)
    have hbi : G.Adj b (c i) := by
      have h := p.adj_getVert_succ (i := 2) (by omega)
      have hend : p.getVert 3 = c i := by simpa [hplen] using p.getVert_length
      simpa [b, hend] using h
    have haNoCycle : ∀ j : Fin 5, ¬G.Adj a (c j) := by
      intro j haj
      have w : G.Walk x (c j) := .cons hxa (.cons haj .nil)
      have hdist2 : G.dist x (c j) ≤ 2 := by simpa using G.dist_le w
      have hmin := hi j
      omega
    have hbnext : ¬G.Adj b (c (i + 1)) := by
      intro h
      exact hTriFree b (c i) (c (i + 1)) hbi (cycle_step_adj hc i) h.symm
    have hxb : ¬G.Adj x b := by
      intro h
      exact hTriFree x a b hxa hab h.symm
    have hxi : ¬G.Adj x (c i) := hnone i
    have hxnext : ¬G.Adj x (c (i + 1)) := hnone (i + 1)
    apply hNoP5 x a b (c i) (c (i + 1))
    unfold FormsInducedP5
    have hstep := cycle_step_adj hc i
    exact ⟨hxa.ne, hxb.ne, hxi.ne, hxnext.ne,
      hab.ne, (haNoCycle i).ne, (haNoCycle (i + 1)).ne,
      hbi.ne, hbnext.ne, hstep.ne,
      hxa, hab, hbi, hstep,
      hxb, hxi, hxnext, haNoCycle i, haNoCycle (i + 1), hbnext⟩

end WrittenOnTheWallII.GraphConjecture314
