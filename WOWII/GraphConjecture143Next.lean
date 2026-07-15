import FormalConjectures.WrittenOnTheWallII.GraphConjecture143

/-!
A short-path lemma for the proof of WOWII Graph Conjecture 143.
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A path with fewer vertices than the girth cannot acquire a cycle when all
edges induced by its support are added. -/
lemma short_path_support_induces_tree {G : SimpleGraph α} {u v : α}
    {p : G.Walk u v} (hp : p.IsPath) (hshort : p.length + 1 < G.girth) :
    (G.induce {x : α | x ∈ p.support}).IsTree := by
  let S : Set α := {x : α | x ∈ p.support}
  have hconn : (G.induce S).Connected := by
    let f : p.toSubgraph.coe →g G.induce S :=
      ⟨fun x => ⟨x.1, by simpa [S, Walk.mem_verts_toSubgraph] using x.2⟩,
        fun h => by simpa using p.toSubgraph.adj_sub h⟩
    apply p.toSubgraph_connected.coe.map f
    intro x
    refine ⟨⟨x.1, ?_⟩, Subtype.ext rfl⟩
    simp [S, x.2]
  refine ⟨hconn, ?_⟩
  intro z c hc
  let incl : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
  have hcG : (c.map incl).IsCycle := hc.map Subtype.val_injective
  have hg : G.girth ≤ c.length := by
    simpa using G.girth_le_length hcG
  have hcard : c.length ≤ Fintype.card S := by
    simpa [S, Walk.length_support] using hc.support_nodup.length_le_card
  have hScard : Fintype.card S = p.length + 1 := by
    rw [← Set.toFinset_card]
    have hfin : S.toFinset = p.support.toFinset := by
      ext x
      simp [S]
    rw [hfin, List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  omega

end WrittenOnTheWallII.GraphConjecture143
