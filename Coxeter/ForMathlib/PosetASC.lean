import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Coxeter.ForMathlib.AbstractSimplicialComplex
import Coxeter.ForMathlib.PosetChain
import Coxeter.ForMathlib.PosetGraded


noncomputable section
open Classical


namespace PartialOrder

open AbstractSimplicialComplex

variable {P : Type*} [PartialOrder P] --[Fintype P] [GradedPoset P]

/-
Definition: Let P be a poset. Let Delta(P) be the set of all chains in P.
Note that each element in Delta(P) will considered as a chain.
-/
@[simp]
def Delta_List (P : Type*) [PartialOrder P] : Set (List P) := {L : List P | chain L}

def Finset.toList' (F : Finset P) (h : IsTrichotomous F (· < ·) ) : List P :=
  List.insertionSort (· < ·) (F.toList)

lemma aux {L : List P} (h : chain L) : IsTrichotomous L.toFinset (· < ·) := by
  sorry

lemma head_sort_of_tail (S : Finset P) (head : P) (g : ∀ s: S, head < s): List.insertionSort (· < ·) (Finset.toList (insert head (S : Finset P))) = head :: (List.insertionSort (· < ·) S.toList) := sorry

lemma aux1 {L : List P} (h : chain L) : Finset.toList' L.toFinset (aux h) = L := by
  rw [Finset.toList']
  induction L with
  | nil => simp
  | cons head tail ih =>
    simp [List.insertionSort_cons_eq_take_drop (· < ·) head tail]
    have g : ∀ s : tail.toFinset, head < s := by
      simp
      sorry
    simp [head_sort_of_tail tail.toFinset head g]
    have g₁ : chain tail := by
      have g₂ : List.Chain' (· < ·) (head :: tail) := by exact h
      have g₃ : List.Chain' (· < ·) (List.tail (head :: tail)) := by apply List.Chain'.tail g₂
      have g₄ : tail = List.tail (head :: tail) := rfl
      rw [g₄] at g₃
      exact g₃
    simp [g₁] at ih
    exact ih
    -- have g : List.insertionSort (· < ·) (Finset.toList (insert head (S : Finset))) ()


lemma aux2 {F₁ F₂ : Finset P} (h : IsTrichotomous F₂ (· < ·)) (hs : F₁ ⊆ F₂) : IsTrichotomous F₁ (· < ·) := by
  constructor
  · intro a b
    let a' : {x // x ∈ F₂} := ⟨a.1, hs a.2⟩
    let b' : {x // x ∈ F₂} := ⟨b.1, hs b.2⟩
    have := h.1 a' b'
    rcases this with h' | h' | h'
    · left; exact h'
    · right; left; ext
      calc
        _ = a'.1 := rfl
        _ = b'.1 := by exact congrArg Subtype.val h'
        _ = b.1 := rfl
    · right; right; exact h'


lemma aux3 {F : Finset P} (h : IsTrichotomous F (· < ·)) : chain (Finset.toList' F h) := sorry

lemma aux4 {F : Finset P} (h : IsTrichotomous F (· < ·)) : List.toFinset (Finset.toList' F h) = F := sorry
/-
Definition: Let P be a poset. Delta P is the set of all chains in P, which is an abstract simplicial complex.
Note that each element in Delta (P) will considered as a subset of P.
-/
@[simp]
abbrev Delta (P : Type*) [PartialOrder P] : AbstractSimplicialComplex P where
  faces := List.toFinset '' Delta_List P
  empty_mem := by simp
  lower' := by
    simp only [IsLowerSet]
    intro a b blea ain
    simp at blea
    simp only [Delta_List, Set.mem_image, Set.mem_setOf_eq]
    simp at ain
    rcases ain with ⟨al, chain_a, ha⟩
    have := aux chain_a
    subst ha
    have := aux2 this blea
    use (Finset.toList' b this)
    constructor
    · simp [aux3]
    · simp [aux4]



/-
Definition: Let P be a graded poset. Then Delta.ASC (P) is a pure abstract simplicial complex.
-/
instance Delta.Pure {P : Type*} [PartialOrder P] [Fintype P] [GradedPoset P]: Pure (Delta P) where
  pure := by
    intro s sin t tin
    have := GradedPoset.pure (P := P)
    simp only [Facets, IsFacet] at *
    sorry





end PartialOrder
