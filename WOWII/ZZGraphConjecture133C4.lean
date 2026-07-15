import FormalConjectures.WrittenOnTheWallII.GraphConjecture133
import WOWII.GraphConjecture143Proof

/-!
The C4-present branch of WOWII Graph Conjecture 133.
-/

namespace WrittenOnTheWallII.GraphConjecture133

open Classical SimpleGraph
open WrittenOnTheWallII.GraphConjecture143

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

lemma geodesic_support_isInducedPath {G : SimpleGraph α} {u v : α}
    {p : G.Walk u v} (hgeo : p.length = G.dist u v) :
    isInducedPath G p.support := by
  have hp : p.IsPath := p.isPath_of_length_eq_dist hgeo
  refine ⟨hp.support_nodup, ?_⟩
  intro i j
  have hi : i.val ≤ p.length := by
    have := i.isLt
    rw [p.length_support] at this
    omega
  have hj : j.val ≤ p.length := by
    have := j.isLt
    rw [p.length_support] at this
    omega
  have hgeti : p.support.get i = p.getVert i.val := by
    simpa using p.support_getElem_eq_getVert i.isLt
  have hgetj : p.support.get j = p.getVert j.val := by
    simpa using p.support_getElem_eq_getVert j.isLt
  rw [hgeti, hgetj]
  constructor
  · intro hadj
    have hedge := geodesic_adj_mem_edges hgeo hi hj hadj
    have hsub : p.toSubgraph.Adj (p.getVert i.val) (p.getVert j.val) :=
      Walk.adj_toSubgraph_iff_mem_edges.mpr hedge
    obtain ⟨k, hk, hklt⟩ := p.toSubgraph_adj_iff.mp hsub
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hk
    rcases hk with ⟨hki, hkj⟩ | ⟨hkj, hki⟩
    · left
      have hik : i.val = k := hp.getVert_injOn hi (by omega) hki.symm
      have hjk : j.val = k + 1 := hp.getVert_injOn hj (by omega) hkj.symm
      omega
    · right
      have hjk : j.val = k := hp.getVert_injOn hj (by omega) hkj.symm
      have hik : i.val = k + 1 := hp.getVert_injOn hi (by omega) hki.symm
      omega
  · rintro (hij | hji)
    · rw [← hij]
      exact p.adj_getVert_succ (by omega)
    · rw [← hji]
      exact (p.adj_getVert_succ (by omega)).symm

lemma induced_path_card_le_path (G : SimpleGraph α) (l : List α)
    (hl : isInducedPath G l) : l.toFinset.card ≤ path G := by
  unfold path
  let P := Finset.univ.filter (fun s : Finset α =>
    ∃ q : List α, q.toFinset = s ∧ isInducedPath G q)
  have hlP : l.toFinset ∈ P := by
    simp [P, hl]
  have hmem : l.toFinset.card ∈ P.image Finset.card :=
    Finset.mem_image.mpr ⟨l.toFinset, hlP, rfl⟩
  have hnon : (P.image Finset.card).Nonempty := ⟨_, hmem⟩
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty hnon
  have hle : l.toFinset.card ≤ m := Finset.le_max_of_eq hmem hm
  simpa [P, hm] using hle

lemma diam_add_one_le_path (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) : G.diam + 1 ≤ path G := by
  obtain ⟨u, v, hd⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp, hgeo⟩ := hG.exists_path_of_dist u v
  have hip : isInducedPath G p.support := geodesic_support_isInducedPath hgeo
  have hle := induced_path_card_le_path G p.support hip
  rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support, hgeo, hd] at hle
  exact hle

lemma radius_toNat_add_one_le_path (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) : G.radius.toNat + 1 ≤ path G := by
  have htop : G.ediam ≠ ⊤ := G.connected_iff_ediam_ne_top.mp hG
  have hrad : G.radius.toNat ≤ G.diam :=
    ENat.toNat_le_toNat G.radius_le_ediam htop
  exact (Nat.add_le_add_right hrad 1).trans (diam_add_one_le_path G hG)

/-- Conjecture 133 holds whenever `G` contains a (not necessarily induced) 4-cycle. -/
theorem conjecture133_of_hasC4 (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hC4 : ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) :
    let rad := G.radius.toNat
    let hasC4 := ∃ a b c d : α,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
    let cC4 : ℕ := if hasC4 then 0 else 1
    (rad : ℝ) + (⌊l G⌋ : ℝ) ^ cC4 ≤ (path G : ℝ) := by
  dsimp only
  rw [if_pos hC4]
  norm_num
  exact_mod_cast radius_toNat_add_one_le_path G hG

end WrittenOnTheWallII.GraphConjecture133
