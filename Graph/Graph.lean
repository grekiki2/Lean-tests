import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Mathlib

structure Graph :=
  vertexSize : Nat
  connected: Fin vertexSize → Fin vertexSize → Prop
  connected_decidable: ∀ a b, Decidable (connected a b) -- Not needed for a graph but makes sense and simplifies proofs
  irreflexive: ∀ n, ¬ connected n n
  symmetric: ∀ a b, connected a b → connected b a

def GraphConnected (G:Graph) (a b:Fin G.vertexSize) : Bool :=
  (G.connected_decidable a b).decide

instance (G:Graph): DecidableRel G.connected := G.connected_decidable

def K_n (k:Nat): Graph :=
  {vertexSize := k
  , connected := (λ x y=>x ≠ y)
  , connected_decidable := by simp; intro a b; apply Not.decidable
  , irreflexive := by simp
  , symmetric := by apply Ne.symm
  }

def C_n (k:Nat) (h:k≥2): Graph :=
  {vertexSize:=k
  , connected:=(λ i j => i.val=j.val+1 || j.val=i.val+1 || (i.val=0 && j.val+1=k) || (j.val=0 && i.val+1=k))
  , connected_decidable := by  intro a b; simp; apply Or.decidable
  , irreflexive := by intro n h2; simp at h2; linarith
  , symmetric:= by intro a b; simp; tauto
  }

def getEdgeListForNode (G:Graph) (i:Fin G.vertexSize) : Array (Fin G.vertexSize) :=
  let ls := List.filter (λ j => GraphConnected G i j) (List.finRange G.vertexSize)
  List.toArray ls
