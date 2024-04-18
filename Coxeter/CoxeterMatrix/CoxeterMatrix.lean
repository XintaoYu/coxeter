import Coxeter.OrderTwoGen
import Coxeter.CoxeterMatrix.TestGroup

/-!
# Coxeter Matrices

This file contains basic definitions and properties of Coxeter matrices.
Then we have a group `G` generated by a set `S` of order 2 elements, proving
a `OrderTwoGen` instance.

# Main Definitions
1. For any `CoxeterMatrix m`, we define a subset `R = toRelationSet m` of relations in the free group `F` over `α`.
2. We define the quptient group `G = F/ < R >`.
3. We denote the image of `α` in `G` by `S`. The set `S` is called the set of simple reflections of `G`.
4. We define a group homomorphism `epsilon` from `G` to the group `μ₂`.
This result relies on the file `TextGroup.lean` for the construction of `μ₂`.
5. We show elements in `S` are all of order 2. So `G` is a group generated by order 2 elements.
-/

open BigOperators

section
variable {α : Type*} [DecidableEq α]
variable (m : Matrix α α ℕ)
/--
Definition of Coxeter matrices:
A square matrix `m` with non-negative integer entries is a Coxeter matrix if it is symmetric, that is, $m_{a,b} = m_{b,a}$ for any (a,b);
the entry $m_{a,b}$ is $1$ if and only if $a=b$.
-/
class CoxeterMatrix : Prop where
  symmetric : ∀ (a b : α), m a b = m b a
  oneIff : ∀ (a b : α), m a b = 1 ↔ a = b
end

open Classical


namespace CoxeterMatrix
variable {α} (m : Matrix α α ℕ) [hm : CoxeterMatrix m]
/-
For the rest of this section, we fix a Coxeter matrix m index by type α with entries in ℕ
-/

/--
This part introduce three lemmas rewriting the definitions.
-/
lemma one_iff : ∀ (a b : α), m a b = 1 ↔ a = b := hm.oneIff

lemma diagonal_one {s : α} : m s s = 1 := by rw [hm.oneIff]

lemma off_diagonal_ne_one {s : α} : s ≠ t → m s t ≠ 1 := by simp [hm.oneIff]
/- We denote by F the free group of type α.
-/
local notation "F" => FreeGroup α

/--
For any `s` and `t` of type `α`, and a natural number `n`, we define a element `(s t) ^ n`
(relation) in the free group `F`.
-/
@[simp] def toRelation (s t : α) (n : ℕ) : F := (FreeGroup.of s * FreeGroup.of t) ^ n

/--
For any `s` of type `α × α`, we define a relation in the free group `F` by $(s_1 s_2)^(m_{s_1, s_2})$
-/
@[simp] def toRelation' (s : α × α) : F := toRelation s.1 s.2 (m s.1 s.2)

/--
We define a set of relations in F by R = {(s_as_b)^{m_{a,b}} | a b ∈ α}.
--/
def toRelationSet : (Set F) := Set.range <| toRelation' m

/--
We define a group `G` by the presentation `⟨α | R⟩`
-/
def toGroup := PresentedGroup <| toRelationSet m

local notation "N" => Subgroup.normalClosure (toRelationSet m)
local notation "G" => toGroup m

/--
The group `G` we just defined is indeed a group.
-/
instance : Group <| toGroup m := QuotientGroup.Quotient.group _

def of (x : α) : G := QuotientGroup.mk' N (FreeGroup.of x)

/-- The set of simple reflections -/
@[simp]
abbrev SimpleRefl := Set.range (of m)

local notation "S" => (SimpleRefl m)

@[simp]
def toSimpleRefl (a : α) : SimpleRefl m := ⟨of m a, by simp⟩

lemma toSimpleRefl_surj (s : S) : ∃ (y : α), toSimpleRefl m y = s := by
  simp only [toSimpleRefl]
  have : s = ⟨s.1, s.2⟩ := by rfl
  rw [this]
  simp only [Subtype.mk.injEq]
  exact Set.mem_range.mp (Subtype.mem s)

lemma toSimpleRefl_surj_list (L : List S) : ∃ (K : List α), K.map (toSimpleRefl m) = L := by
  induction L with
  | nil => simp only [SimpleRefl, List.map_eq_nil, exists_eq]
  | cons hd tail ih =>
    rcases ih with ⟨l, el⟩
    rcases (toSimpleRefl_surj m hd) with ⟨y, ey⟩
    use y :: l
    rw [List.map_cons]
    congr

instance coe_group: Coe α (toGroup m) where
  coe := of m

instance coe_simple_refl: Coe α (SimpleRefl m) where
  coe := toSimpleRefl m

lemma liftHom_aux {A:Type*} [Group A] (f : α → A) (h : ∀ (s t : α), (f s * f t) ^ (m s t) = 1) : ∀ r ∈ toRelationSet m, (FreeGroup.lift f) r = 1 := by
  intro r hr
  obtain ⟨⟨s, t⟩, hst⟩ := hr
  simp only [toRelation', toRelation] at hst
  simp only [← hst, map_pow, map_mul, FreeGroup.lift.of, h]

/-- Lift map from α → A to Coxeter group → A -/
def lift {A : Type _} [Group A] (f : α → A) (h : ∀ (s t : α), (f s * f t) ^ (m s t) = 1) : G →* A := PresentedGroup.toGroup <| liftHom_aux m f h

lemma lift.of {A : Type _} [Group A] (f : α → A) (h : ∀ (s t : α), (f s * f t) ^ (m s t) = 1) (s : α) : lift m f h (of m s) = f s := by
  apply PresentedGroup.toGroup.of

open TestGroup

/-- We define (and prove) a group homomorphism from `G` to `μ₂`
by mapping each simple reflection to the generator of `μ₂`.
-/
@[simp]
def epsilon : G →* μ₂ := lift m (fun _=> μ₂.gen) (by intro s t; ext; simp)

lemma epsilon_of (s : α) : epsilon m (of m s) = μ₂.gen := by
  simp only [epsilon, lift.of m]

lemma epsilon_S {a : S} : epsilon m a = μ₂.gen := by
  simp only [epsilon, lift.of m]
  aesop

@[simp]
lemma of_relation (s t: α) : ((of m s) * (of m t))^(m s t) = 1 := by
  set M := toRelationSet m
  set k := ((FreeGroup.of s) * (FreeGroup.of t))^(m s t)
  have kM : (k ∈ M) := by exact Exists.intro (s, t) rfl
  have MN : (M ⊆ N) := by exact Subgroup.subset_normalClosure
  have kN : (k ∈ N) := by exact MN kM
  rw [of, of]
  have : (((QuotientGroup.mk' N) (FreeGroup.of s) * (QuotientGroup.mk' N) (FreeGroup.of t)) ^ (m s t)
    = (QuotientGroup.mk' N) ((FreeGroup.of (s) * FreeGroup.of (t)) ^ (m s t))) := by rfl
  rw [this]
  apply (QuotientGroup.eq_one_iff k).2
  exact kN

lemma of_square_eq_one {s : α} : (of m s) * (of m s) = 1 := by
  have : m s s = 1 := diagonal_one m
  rw [← pow_one ((of m s) * (of m s)), ←this]
  apply of_relation m s s

@[simp]
lemma of_square_eq_one' : s ∈ SimpleRefl m → s * s = 1 := by
  simp only [SimpleRefl, Set.mem_range, forall_exists_index]
  intro x h
  simp_all only [← h, of_square_eq_one]

lemma of_inv_eq_of {x : α} : (of m x)⁻¹ = of m x :=
  inv_eq_of_mul_eq_one_left (@of_square_eq_one α m hm x)

lemma SimpleRefl_closed_under_inverse : S = S⁻¹ := by
  ext y
  constructor
  . rintro ⟨w, hw⟩
    use w
    rw [← hw, of_inv_eq_of]
  . rintro ⟨w, hw⟩
    use w
    rw [← inv_inj, ← hw, of_inv_eq_of]

/- Lemma: The group `G` is generated by the set S.
-/
lemma toGroup_expression : ∀ (x : G), ∃ L : List S, x = L.gprod := by
  intro x
  apply (Submonoid.mem_monoid_closure_iff_prod S x).1
  have h₀ : S = S ∪ S⁻¹ := by rw [← SimpleRefl_closed_under_inverse, Set.union_self]
  have h₁ : Subgroup.closure S = ⊤ := by
    rw [SimpleRefl, Set.range]
    simp only [of, toGroup, PresentedGroup]
    have : Subgroup.closure {x | ∃ y, (QuotientGroup.mk' N) (FreeGroup.of y) = x}
      = Subgroup.closure (Set.range (PresentedGroup.of)) := rfl
    rw [this, PresentedGroup.closure_range_of]
  rw [h₀, ← Subgroup.closure_toSubmonoid, Subgroup.mem_toSubmonoid, h₁]
  trivial

def getS (L: List (α × Bool)) := L.map (fun (a, _) => toSimpleRefl m a)

@[deprecated toGroup_expression]
lemma toGroup_expression' : ∀ (x : G), ∃ L : List S, x = L.gprod := by
  intro x
  have k : ∃ y : F, QuotientGroup.mk y = x := by exact Quot.exists_rep x
  rcases k with ⟨y, rep⟩
  set a := getS m y.toWord
  use a
  have : x = a.gprod := by
    simp only [a]
    rw [getS, ← rep]
    set L := FreeGroup.toWord y with hL
    have : FreeGroup.mk L = y := by
      rw [hL]
      exact FreeGroup.mk_toWord
    rw [← this]
    induction L with
    | nil =>
      norm_num1
      rw [← FreeGroup.toWord_one, FreeGroup.mk_toWord]
      simp only [QuotientGroup.mk_one, SimpleRefl, toSimpleRefl,
        FreeGroup.toWord_one, List.map_nil, gprod_nil]
    | cons hd tail ih =>
      rw [List.map_cons, ← List.singleton_append, ← FreeGroup.mul_mk]
      rw [gprod_cons, ← ih]
      rw [QuotientGroup.mk_mul]
      simp only [mul_left_inj]
      by_cases h : hd.2
      · congr
        exact Prod.snd_eq_iff.mp h
      · push_neg at h
        have h' : hd.2 = false := Bool.eq_false_iff.mpr h
        have h'' : QuotientGroup.mk' N (FreeGroup.mk ([(hd.1, true)] ++ [(hd.1, true)])) = 1 := by
          rw [← FreeGroup.mul_mk, ← FreeGroup.of]
          have : (QuotientGroup.mk' N) (FreeGroup.of hd.1 * FreeGroup.of hd.1) =
            (QuotientGroup.mk' N) (FreeGroup.of hd.1) * (QuotientGroup.mk' N) (FreeGroup.of hd.1)
            := rfl
          rw [this, ← of, of_square_eq_one]
        simp only [QuotientGroup.mk'_apply] at h''
        rw [← FreeGroup.mul_mk, QuotientGroup.mk_mul,
          ← mul_right_inv (↑(FreeGroup.mk [(hd.1, true)])), mul_right_inj,
          ← QuotientGroup.mk_inv, FreeGroup.inv_mk, FreeGroup.invRev] at h''
        simp only [List.map_cons, Bool.not_true, List.map_nil, List.reverse_cons, List.reverse_nil,
          List.nil_append] at h''
        have : hd = (hd.1, false) := Prod.snd_eq_iff.mp h'
        nth_rw 1 [this]
        rw [← h'']
        rfl
  apply this

/--
Lemma: Let `s ∈ S` be a generator of `G`, then `s` is non-trivial.
-/
lemma generator_ne_one (s : α) : of m s ≠ 1 := by
  intro h
  have h1 : epsilon m (of m s) = 1 := by rw [h]; simp
  have h2 : epsilon m (of m s) = μ₂.gen := by rw [epsilon_of]
  rw [h2] at h1; exact μ₂.gen_ne_one h1

/--
Lemma: Let `s ∈ S` be a generator of `G`, then `s` is non-trivial.
-/
lemma generator_ne_one' {x : G} : x ∈ S → x ≠ 1 := by
  rintro ⟨s, hs⟩
  rw [← hs]
  exact generator_ne_one m s

/--
Lemma: Let `s ∈ S` be a generator of `G`, then `s^2 = 1` and `s ≠ 1`.
-/
lemma order_two : ∀ (x : G), x ∈ S → x * x = (1 : G) ∧ x ≠ 1 := by
  rintro x ⟨s, hs⟩
  rw [← hs]
  exact ⟨of_square_eq_one m, generator_ne_one m s⟩

/--
Instance: The group `G` with the generating set `S` is a group generators by order 2 elements.
-/
instance ofOrderTwoGen : OrderTwoGen (SimpleRefl m) where
  order_two := order_two m
  expression := toGroup_expression m

end CoxeterMatrix
