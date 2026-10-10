import Holant.Complexity.FixedGadgetSubstitution.PresentedScaledFamily

/-! Projectively adjoining any fixed algebraic output of an ordinary macro.
The common coefficient field is derived from the original entries and the fixed
output entries. Auxiliary field coordinates do not become target signatures. -/
namespace Holant.Complexity.FixedGadgetSubstitution.AlgebraicProjectiveAdjoin
open Computability Holant.Algebraic ExactSignatureTables
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {L : Type} [Field L] [Algebra ℚ L] {s b : ℕ} {arity : ℕ → ℕ}
variable (coeff : CoefficientIndex s b arity → L)
variable (halg : ∀a,IsAlgebraic ℚ (coeff a))
variable (g : Template) (hg : g.WellFormed s b arity)
variable (q : Signature L g.boundary) (hqalg : ∀x,IsAlgebraic ℚ (q x))

def values : CoefficientIndex s b arity ⊕ (Fin g.boundary → Bool) → L :=
  Sum.elim coeff q

include halg hqalg in
theorem values_algebraic : ∀a,IsAlgebraic ℚ (values coeff g q a) := by
  intro a
  cases a with
  | inl a => exact halg a
  | inr x => exact hqalg x

abbrev presentation := familyPresentation (values coeff g q)
  (values_algebraic coeff halg g q hqalg)

abbrev originalTables := PresentedScaledFamily.tables (values coeff g q)
  (values_algebraic coeff halg g q hqalg) Sum.inl

def scaleAt (p : Fin g.boundary → Bool) : familyField (values coeff g q) :=
  (g.network hg
    (fun i x => (presentation coeff halg g q hqalg).decode
      ((originalTables coeff halg g q hqalg).vertex i x))
    (fun i a b => (presentation coeff halg g q hqalg).decode
      ((originalTables coeff halg g q hqalg).edge i a b))).denote p /
    fieldCoefficient (values coeff g q) (.inr p)

theorem scaleAt_value (c : L)
    (hmacro : (OriginalFamily.ambientMacro coeff g hg).denote=c • q)
    (p : Fin g.boundary → Bool) (hp : q p≠0) :
    (scaleAt coeff halg g hg q hqalg p : L)=c := by
  unfold scaleAt
  rw [Subfield.coe_div]
  rw [PresentedScaledFamily.macro_value_exact]
  change (OriginalFamily.ambientMacro coeff g hg).denote p/q p=c
  rw [hmacro]
  change c*q p/q p=c
  exact mul_div_cancel_right₀ c hp

theorem scaleAt_ne_zero (c : L) (hc : c≠0)
    (hmacro : (OriginalFamily.ambientMacro coeff g hg).denote=c • q)
    (p : Fin g.boundary → Bool) (hp : q p≠0) :
    scaleAt coeff halg g hg q hqalg p≠0 := by
  intro h
  have he := scaleAt_value coeff halg g hg q hqalg c hmacro p hp
  rw [h] at he
  exact hc he.symm

theorem normalized_macro (c : L) (hc : c≠0)
    (hmacro : (OriginalFamily.ambientMacro coeff g hg).denote=c • q)
    (p : Fin g.boundary → Bool) (hp : q p≠0) :
    (fun x => (OriginalFamily.ambientMacro coeff g hg).denote x /
      (scaleAt coeff halg g hg q hqalg p:L))=q := by
  funext x
  rw [scaleAt_value coeff halg g hg q hqalg c hmacro p hp,hmacro]
  change c*q x/c=q x
  exact mul_div_cancel_left₀ (q x) hc

theorem source_family_exact (c : L) (hc : c≠0)
    (hmacro : (OriginalFamily.ambientMacro coeff g hg).denote=c • q)
    (p : Fin g.boundary → Bool) (hp : q p≠0) :
    Set.range (fun i : Fin (s+1) =>
      (⟨sourceArity (Adjoin.templates s arity g) i.val,
        PresentedScaledFamily.ambientSource (values coeff g q) Sum.inl g hg
          (scaleAt coeff halg g hg q hqalg p) i⟩ : AnySignature L)) =
    Set.range (fun i : Fin s =>
      (⟨arity i.val,fun x => coeff (.inl ⟨i,x⟩)⟩ : AnySignature L)) ∪ {⟨g.boundary,q⟩} := by
  rw [PresentedScaledFamily.ambientSource_family]
  change _ ∪ {(⟨g.boundary,fun x => (OriginalFamily.ambientMacro coeff g hg).denote x /
    (scaleAt coeff halg g hg q hqalg p:L)⟩ : AnySignature L)} = _
  rw [normalized_macro coeff halg g hg q hqalg c hc hmacro p hp]
  rfl

abbrev ReductionType (p : Fin g.boundary → Bool) :=
  PresentedScaledFamily.ReductionType (values coeff g q)
    (values_algebraic coeff halg g q hqalg) Sum.inl g hg
    (scaleAt coeff halg g hg q hqalg p)

def reduction (c : L) (hc : c≠0)
    (hmacro : (OriginalFamily.ambientMacro coeff g hg).denote=c • q)
    (p : Fin g.boundary → Bool) (hp : q p≠0) :
    ReductionType coeff halg g hg q hqalg p :=
  PresentedScaledFamily.reduction (values coeff g q)
    (values_algebraic coeff halg g q hqalg) Sum.inl g hg
    (scaleAt coeff halg g hg q hqalg p)
    (scaleAt_ne_zero coeff halg g hg q hqalg c hc hmacro p hp)

theorem nonempty_reduction (c : L) (hc : c≠0)
    (hmacro : (OriginalFamily.ambientMacro coeff g hg).denote=c • q) (hq : q≠0) :
    ∃p,Nonempty (ReductionType coeff halg g hg q hqalg p) := by
  have hx : ∃x,q x≠0 := by
    by_contra h
    push_neg at h
    exact hq (funext h)
  obtain ⟨p,hp⟩ := hx
  exact ⟨p,⟨reduction coeff halg g hg q hqalg c hc hmacro p hp⟩⟩

/- The original target problem is unchanged, even when its answer is written
in the derived larger fixed field. No auxiliary value is a vertex label. -/
theorem target_value_exact (r : Input s b arity) :
    (((originalTables coeff halg g q hqalg).evaluate
      (presentation coeff halg g q hqalg) r : familyField (values coeff g q)) : L) =
    (r.val.realize r.property (fun i x => coeff (.inl ⟨i,x⟩))
      (fun i a b => coeff (.inr (i,a,b)))).denote Fin.elim0 :=
  PresentedScaledFamily.target_value_exact (values coeff g q)
    (values_algebraic coeff halg g q hqalg) Sum.inl r
end
end Holant.Complexity.FixedGadgetSubstitution.AlgebraicProjectiveAdjoin
