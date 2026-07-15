import FormalConjectures.WrittenOnTheWallII.GraphConjecture160

namespace WrittenOnTheWallII.GraphConjecture160

open Classical SimpleGraph

/-- `K_{2,3}` with one additional edge inside the three-vertex part. -/
def counterexample160 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet
    {s(0,2), s(0,3), s(0,4), s(1,2), s(1,3), s(1,4), s(2,4)}

/-- A concrete spanning tree of `counterexample160`. -/
def counterexample160Tree : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0,2), s(0,3), s(0,4), s(1,2)}

lemma counterexample160_connected : counterexample160.Connected := by
  native_decide

lemma counterexample160Tree_le : counterexample160Tree ≤ counterexample160 := by
  native_decide

lemma counterexample160Tree_isTree : counterexample160Tree.IsTree := by
  native_decide

lemma counterexample160_max_local_independence :
    (Finset.univ.image (indepNeighborsCard counterexample160)).max' (by simp) = 2 := by
  simp only [indepNeighborsCard]
  simp_rw [indep_num_eq_computable]
  native_decide

lemma counterexample160_max_triangles :
    maxTrianglesAtVertex counterexample160 = 2 := by
  unfold maxTrianglesAtVertex numTrianglesAtVertex
  native_decide

lemma counterexample160_induced_C4_count :
    countInducedC4 counterexample160 = 2 := by
  unfold countInducedC4 isInducedC4
  native_decide

/-- The maximum number of leaves of a spanning tree never exceeds the number of vertices. -/
lemma Ls_le_card {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    Ls G ≤ Fintype.card α := by
  unfold Ls
  dsimp only
  apply csSup_le
  · obtain ⟨T, hTG, hTtree⟩ := hG.exists_isTree_le
    let H : G.Subgraph := T.toSubgraph hTG
    have hspan : H.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hTG
    have htree : H.coe.IsTree := by
      rw [← (H.spanningCoeEquivCoeOfSpanning hspan).isTree_iff]
      simpa [H, SimpleGraph.toSubgraph, Subgraph.spanningCoe] using hTtree
    exact Set.image_nonempty.mpr ⟨H, hspan, htree⟩
  · rintro y ⟨H, hH, rfl⟩
    have hcard :
        (H.verts.toFinset.filter (fun v => H.degree v = 1)).card ≤ Fintype.card α := by
      calc
        (H.verts.toFinset.filter (fun v => H.degree v = 1)).card
            ≤ H.verts.toFinset.card := Finset.card_filter_le _ _
        _ = Fintype.card α := by
          rw [hH.1.verts_eq_univ]
          simp
    exact_mod_cast hcard

lemma counterexample160_Ls_le_five : Ls counterexample160 ≤ 5 := by
  simpa using Ls_le_card counterexample160 counterexample160_connected

/-- The five-vertex graph violates WOWII Conjecture 160: its proposed lower bound is 6,
while every spanning tree has at most five leaves. -/
theorem counterexample160_refutes_statement :
    ¬ (let maxL :=
          (Finset.univ.image (fun v => indepNeighborsCard counterexample160 v)).max' (by simp)
       let maxT := maxTrianglesAtVertex counterexample160
       let cC4 := countInducedC4 counterexample160
       (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls counterexample160) := by
  simp only [counterexample160_max_local_independence,
    counterexample160_max_triangles, counterexample160_induced_C4_count]
  linarith [counterexample160_Ls_le_five]

-- CI iteration marker 2.
end WrittenOnTheWallII.GraphConjecture160
