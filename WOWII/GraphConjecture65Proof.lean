import FormalConjectures.WrittenOnTheWallII.GraphConjecture65

/-!
A direct proof of Written on the Wall II Graph Conjecture 65.
-/

namespace WrittenOnTheWallII.GraphConjecture65

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma exists_crossing_edge {G : SimpleGraph α} (hG : G.Connected)
    {S : Set α} (hS : S.Nonempty) (hS_ne : S ≠ Set.univ) :
    ∃ u ∈ S, ∃ v ∉ S, G.Adj u v := by
  by_contra hcross
  push_neg at hcross
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := Set.ne_univ_iff_exists_not_mem.mp hS_ne
  let H : G.Subgraph where
    verts := S
    Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
    adj_sub h := h.1
    edge_vert h := h.2.1
    symm := by
      intro x y hxy
      exact ⟨hxy.1.symm, hxy.2.2, hxy.2.1⟩
  have hvS : v ∈ H.verts := (hG u v).mem_subgraphVerts (H := H) (by
    intro x hx y hxy
    have hy : y ∈ S := by
      by_contra hy
      exact hcross x hx y hy hxy
    exact ⟨hxy, hx, hy⟩) hu
  exact hv hvS

lemma distMin_le_one {G : SimpleGraph α} [DecidableRel G.Adj]
    (hG : G.Connected) {S : Set α} (hS : S.Nonempty) :
    distMin G S ≤ 1 := by
  by_cases hS_univ : S = Set.univ
  · subst S
    simp [distMin]
  · obtain ⟨u, hu, v, hv, huv⟩ := exists_crossing_edge hG hS hS_univ
    unfold distMin
    let outside := Finset.univ.filter (fun w : α => w ∉ S)
    have hvout : v ∈ outside := by simp [outside, hv]
    rw [dif_pos ⟨v, hvout⟩]
    have hmin :
        (outside.image (fun w => distToSet G w S)).min'
            (Finset.Nonempty.image ⟨v, hvout⟩ _) ≤ distToSet G v S := by
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨v, hvout, rfl⟩
    have hdist : distToSet G v S ≤ G.dist v u := by
      unfold distToSet
      rw [dif_pos hS]
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨u, by simpa using hu, rfl⟩
    have hdvu : G.dist v u = 1 := dist_eq_one_iff_adj.mpr huv.symm
    omega

lemma two_le_largestInducedForestSize (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) [Nontrivial α] :
    2 ≤ G.largestInducedForestSize := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne α
  obtain ⟨w, huw⟩ := (hG u v).nonempty_neighborSet_left huv
  unfold largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨s, _, rfl⟩
      exact s.card_le_univ⟩
  · refine ⟨{u, w}, ?_, by simp [huw.ne]⟩
    apply IsAcyclic.of_card_le_two
    simp [huw.ne]

/-- WOWII Conjecture 65. The two distance-minimum terms contribute at most two,
and every nontrivial connected graph contains an induced two-vertex forest. -/
theorem conjecture65_proved [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) :
    let A : Set α := {v | G.degree v = G.minDegree}
    let M : Set α := {v | G.degree v = G.maxDegree}
    (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤
      (G.largestInducedForestSize : ℝ) := by
  let A : Set α := {v | G.degree v = G.minDegree}
  let M : Set α := {v | G.degree v = G.maxDegree}
  have hA_nonempty : A.Nonempty := by
    obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
    exact ⟨v, hv⟩
  have hM_nonempty : M.Nonempty := by
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    exact ⟨v, hv⟩
  have hA := distMin_le_one hG hA_nonempty
  have hM := distMin_le_one hG hM_nonempty
  have hleft :
      (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤ 2 := by
    have hA_cases : distMin G A = 0 ∨ distMin G A = 1 := by omega
    have hM_cases : distMin G M = 0 ∨ distMin G M = 1 := by omega
    rcases hA_cases with hA0 | hA1 <;>
      rcases hM_cases with hM0 | hM1 <;>
      simp [hA0, hA1, hM0, hM1]
  have hforest : (2 : ℝ) ≤ (G.largestInducedForestSize : ℝ) := by
    exact_mod_cast two_le_largestInducedForestSize G hG
  dsimp only
  exact hleft.trans hforest

end WrittenOnTheWallII.GraphConjecture65
