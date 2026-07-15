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
  have hex : ∃ v : α, v ∉ S := by
    by_contra h
    push_neg at h
    apply hS_ne
    ext x
    simp [h x]
  obtain ⟨v, hv⟩ := hex
  let H : G.Subgraph where
    verts := S
    Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
    adj_sub h := h.1
    edge_vert h := h.2.1
    symm.symm := by
      rintro x y ⟨hxy, hx, hy⟩
      exact ⟨hxy.symm, hy, hx⟩
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
    dsimp only
    have hvout : v ∈ Finset.univ.filter (fun w : α => w ∉ S) := by simp [hv]
    have hout : (Finset.univ.filter (fun w : α => w ∉ S)).Nonempty := ⟨v, hvout⟩
    rw [dif_pos hout]
    have hmin :
        ((Finset.univ.filter (fun w : α => w ∉ S)).image
          (fun w => distToSet G w S)).min' (Finset.Nonempty.image hout _) ≤
          distToSet G v S := by
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨v, hvout, rfl⟩
    have hSfin : S.toFinset.Nonempty := by
      simpa [Finset.Nonempty] using hS
    have hdist : distToSet G v S ≤ G.dist v u := by
      unfold distToSet
      rw [dif_pos hSfin]
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨u, by simpa using hu, rfl⟩
    have hdvu : G.dist v u = 1 := dist_eq_one_iff_adj.mpr huv.symm
    omega

lemma two_le_largestInducedForestSize (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) [Nontrivial α] :
    2 ≤ G.largestInducedForestSize := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne α
  obtain ⟨w, huw⟩ := Reachable.nonempty_neighborSet_left huv (hG u v)
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
    exact ⟨v, hv.symm⟩
  have hM_nonempty : M.Nonempty := by
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    exact ⟨v, hv.symm⟩
  have hA := distMin_le_one hG hA_nonempty
  have hM := distMin_le_one hG hM_nonempty
  have hAreal : (distMin G A : ℝ) ≤ 1 := by exact_mod_cast hA
  have hceilInt : ⌈(distMin G M : ℝ) / 3⌉ ≤ (1 : ℤ) := by
    rw [Int.ceil_le]
    have hMreal : (distMin G M : ℝ) ≤ 1 := by exact_mod_cast hM
    linarith
  have hceil : (⌈(distMin G M : ℝ) / 3⌉ : ℝ) ≤ 1 := by
    exact_mod_cast hceilInt
  have hleft :
      (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤ 2 := by
    linarith
  have hforest : (2 : ℝ) ≤ (G.largestInducedForestSize : ℝ) := by
    exact_mod_cast two_le_largestInducedForestSize G hG
  dsimp only
  exact hleft.trans hforest

end WrittenOnTheWallII.GraphConjecture65
