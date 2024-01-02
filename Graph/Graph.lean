import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Mathlib

structure Graph : Type :=
  vertexSize : Nat
  connected: Fin vertexSize → Fin vertexSize → Prop
  connected_decidable: ∀ a b, Decidable (connected a b) -- Not needed for a graph but makes sense and simplifies proofs
  irreflexive: ∀ n, ¬ connected n n
  symmetric: ∀ a b, connected a b → connected b a

def GraphConnected (G:Graph) (a b:Fin G.vertexSize) : Bool :=
  (G.connected_decidable a b).decide

def valid_coloring (G:Graph) (coloring: Fin G.vertexSize → Fin k): Prop :=
  ∀ a b, GraphConnected G a b → coloring a ≠ coloring b

def G_example : Graph := {vertexSize:=4, connected:=(λ x y=>x ≠ y), connected_decidable := by {simp; intro a b;apply Not.decidable}, irreflexive := by simp, symmetric:= by {apply Ne.symm} }

instance (G:Graph): DecidableRel G.connected := G.connected_decidable

#eval G_example.vertexSize

#eval G_example.connected ⟨0, by decide⟩ ⟨0, by decide⟩


structure Graph2 : Type :=
  vertexSize : Nat
  edgeList: Array (Array (Fin vertexSize))
  edgeListSize: edgeList.size = vertexSize
  edgeIrreflexive: ∀ i:Fin vertexSize, ¬ i ∈ edgeList[i]'(by {rw [edgeListSize]; exact Fin.prop i})
  edgeSymmetric: ∀ i j: Fin vertexSize,
    j ∈ edgeList[i]'(by {rw [edgeListSize]; exact Fin.prop i}) →
    i ∈ edgeList[j]'(by {rw [edgeListSize]; exact Fin.prop j})

def Graph2Connected (G2: Graph2) (i j:Fin G2.vertexSize) : Bool :=
  Array.contains (G2.edgeList[i]'(by {rw [G2.edgeListSize]; exact Fin.prop i})) j

def valid_coloring2 (G2:Graph2) (coloring: Fin G2.vertexSize → Fin k): Prop :=
  ∀ i j:Fin G2.vertexSize, Graph2Connected G2 i j → coloring i ≠ coloring j

-- Plan: konverzijske funkcije iz Graph v Graph2 in obratno, dokaz bijektivnosti?, dokaz da valid_coloring2 inducira valid_coloring
-- Potem pa lahko definiramo fukncijo ki dejansko izracuna coloring na Graph2, dokazemo da je pravilna
-- Nato definiramo wrapper ki najde pravilen coloring na grafu 1 s konverzijo v graf2, barvanjem na graf2 in transportom barvanja nazaj

def getEdgeListForNode (G:Graph) (i:Fin G.vertexSize) : Array (Fin G.vertexSize) :=
  let ls := List.filter (λ j => GraphConnected G i j) (List.finRange G.vertexSize)
  List.toArray ls

def getEdgeListGtoG2 (G:Graph) : Array (Array (Fin G.vertexSize)) :=
  let ls := List.map (λ idx => getEdgeListForNode G idx) (List.finRange G.vertexSize)
  List.toArray ls

#check Array.toArray_data
#check Array.data_toArray
lemma list_array_idx_equiv (as: List α) (idx: Fin as.length): (List.toArray as)[idx] = as[idx] := by
  have q2:= Array.getElem_fin_eq_data_get (List.toArray as) ⟨idx.val, by simp⟩
  simp at q2 ⊢
  rw [q2]
  refine (List.get_of_eq ?_ idx).symm
  exact (List.toArray_data as).symm

lemma array_idx_val_equiv (as: Array α) (idx: Fin as.size): as[idx.val] = as[idx] := by
  rfl

lemma list_array_idx_val_equiv (as: List α) (idx: Fin as.length): (List.toArray as)[idx.val] = as[idx] := by
  rw [array_idx_val_equiv (List.toArray as) ⟨idx.val, by simp⟩]
  exact list_array_idx_equiv as idx

#eval getEdgeListGtoG2 G_example
#check List.of_mem_filter
#check List.mem_filter
theorem Array.mem_iff_contains {α : Type _} [DecidableEq α] {a : α} {as : Array α} : a ∈ as ↔ as.contains a := by
  exact Iff.symm contains_def

def convertGraphToGraph2 (G:Graph) : Graph2 :=
  {vertexSize := G.vertexSize, edgeList:= getEdgeListGtoG2 G, edgeListSize:=by {simp [getEdgeListGtoG2]
  }, edgeIrreflexive:=by {
    intro i
    unfold getEdgeListGtoG2
    simp
    rw [list_array_idx_val_equiv _ ⟨i.val, by simp⟩]
    simp
    unfold getEdgeListForNode
    simp
    intro h
    have q:=List.of_mem_filter h
    unfold GraphConnected at q
    have j:= G.irreflexive i
    simp [j] at q
  }, edgeSymmetric:= by{
    intro i j hj
    unfold getEdgeListGtoG2 at hj ⊢
    simp at hj ⊢
    rw [list_array_idx_val_equiv _ ⟨j.val, by simp⟩ ]
    rw [list_array_idx_val_equiv _ ⟨i.val, by simp⟩ ] at hj
    simp at hj ⊢
    unfold getEdgeListForNode at hj ⊢
    simp at hj ⊢
    have q:= List.of_mem_filter hj
    rw [List.mem_filter]
    simp
    unfold GraphConnected at q ⊢
    simp at q ⊢
    exact Graph.symmetric G i j q
  }}

#eval (convertGraphToGraph2 (G_example)).edgeList

lemma list_array_contains_eq {α : Type} [DecidableEq α] (as : List α) (b : α) : Array.contains (List.toArray as) b = List.contains as b := by
  refine Bool.eq_iff_eq_true_iff.mpr ?_
  constructor
  · intro h
    have q:= Array.contains_def.mp h
    have q2:= q.val
    rw [Array.data_toArray] at q2
    exact List.elem_iff.mpr q2
  · intro h
    apply Array.contains_def.mpr
    suffices b ∈ (List.toArray as).data by {
      exact (Array.mem_def b (List.toArray as)).mpr this
    }
    rw [Array.data_toArray]
    exact List.mem_of_elem_eq_true h


lemma in_rw (as: List Nat) (b:Nat): List.contains as b = (b ∈ as) := by
  refine (propext ?_).symm
  constructor
  · exact List.elem_eq_true_of_mem
  · exact List.mem_of_elem_eq_true

#check List.elem_eq_true_of_mem
#check List.mem_of_elem_eq_true
#check List.mem_filter -- Maybe we can refactor with this
lemma list_contains_filter  {α : Type u} [BEq α] [LawfulBEq α] (as: List α) (b:α) (p:α → Bool): List.contains (List.filter p as) b = (List.contains as b ∧ p b) := by
  simp
  constructor
  · induction as with
    | nil => simp [List.filter]
    | cons a as ih =>
      by_cases h : p a <;> simp [h, or_and_right]
      · intro h
        rcases h with h2|h2
        · apply Or.inl
          simp [h2]
          trivial
        · specialize ih h2
          exact Or.inr ih
      · intro h2
        exact Or.inr (ih h2)
  · intro ⟨hl, hr⟩
    refine List.elem_eq_true_of_mem ?mpr.h
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_of_elem_eq_true hl
    · assumption


#check list_contains_filter

theorem connected_iff (G:Graph): GraphConnected G = Graph2Connected (convertGraphToGraph2 G) := by
  unfold GraphConnected Graph2Connected
  funext i j
  unfold convertGraphToGraph2 getEdgeListGtoG2 getEdgeListForNode
  simp
  rw [list_array_idx_val_equiv _ ⟨i.val, by {simp}⟩]
  simp
  rw [list_array_contains_eq]
  match h:decide (Graph.connected G i j) with
  | true =>
    apply Eq.symm
    rw [list_contains_filter]
    simp
    exact h
  | false =>
    apply Eq.symm
    match h2:List.contains (List.filter (fun j => GraphConnected G i j) (List.finRange G.vertexSize)) j with
    | true =>
      rw [list_contains_filter] at h2
      simp at h2
      unfold GraphConnected at h2
      rw [h] at h2
      exact h2.symm
    | false => rfl

theorem colorings_convert (G: Graph) (coloring: Fin G.vertexSize → Fin k): valid_coloring G coloring ↔ valid_coloring2 (convertGraphToGraph2 G) coloring := by
  constructor
  · intro h
    unfold valid_coloring at h
    unfold valid_coloring2
    intro i j cij
    rw [← connected_iff] at cij
    exact h i j cij
  · intro h
    unfold valid_coloring2 at h
    unfold valid_coloring
    intro i j cij
    rw [connected_iff] at cij
    exact h i j cij
