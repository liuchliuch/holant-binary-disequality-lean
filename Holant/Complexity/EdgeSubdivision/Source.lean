import Holant.Complexity.EdgeSubdivision.WireFamily
import Holant.Algebraic.FiniteFamilyNetwork

/-! Source Lemma 5.1. Both reductions use a coefficient field derived from the
original fixed finite algebraic signatures. The graph input contains no field,
component, path, cycle, or compiler certificate. -/
namespace Holant.Complexity.EdgeSubdivision.Source
open Computability Holant.Algebraic ExactSignatureTables
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {L : Type} [Field L] [Algebra ℚ L] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature L (arity i.val))
variable (halg : ∀ i x,IsAlgebraic ℚ (G i x))

def coefficient : CoefficientIndex s 1 arity → L
  | .inl ⟨i,x⟩ => G i x
  | .inr (_,a,b) => Signature.equality a b

include halg in
theorem coefficient_algebraic : ∀ a,IsAlgebraic ℚ (coefficient G a) := by
  intro a
  cases a with
  | inl a => exact halg a.1 a.2
  | inr a =>
    rcases a with ⟨i,a,b⟩
    cases a <;> cases b <;> first | exact isAlgebraic_zero | exact isAlgebraic_one

abbrev field := familyField (coefficient G)
abbrev presentation := familyPresentation (coefficient G) (coefficient_algebraic G halg)

def coordinates (i : Fin s) (x : Fin (arity i.val) → Bool) :
    Fin (Module.finrank ℚ (field G)) → ℚ :=
  familyCoordinates (coefficient G) (coefficient_algebraic G halg) (.inl ⟨i,x⟩)

abbrev tables (p q : Bool) :=
  WireEquivalence.tables (presentation G halg) (coordinates G halg) p q

abbrev problem (p q : Bool) : WireEquivalence.Input s arity → field G :=
  (tables G halg p q).evaluate (presentation G halg)

abbrev Reduction (p q : Bool) := PolyTimeOracleReduction
  (RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s arity)) (presentation G halg).encoding
  (RawClosedNetwork.validatedEncoding (s+1) 1 (targetArity s arity)) (presentation G halg).encoding
  (problem G halg p q) (problem G halg q p)

/-- The answer decodes to the unchanged ambient signature set and literal wire,
including zero values, nullary factors and arbitrary ordered closed incidence. -/
theorem value_exact (p q : Bool) (r : WireEquivalence.Input s arity) :
    ((problem G halg p q r : field G) : L) = WireEquivalence.value G p q r := by
  unfold problem tables
  rw [WireEquivalence.evaluate_eq]
  unfold WireEquivalence.value
  change (field G).subtype _ = _
  rw [←Network.denote_map (field G).subtype]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    dsimp only
    unfold extendedSignatures
    split
    · exact familyCoordinates_spec (coefficient G) (coefficient_algebraic G halg) _
    · simp [WirePath.kernel]
  · funext e a b
    simp [WirePath.kernel]

/-- Full equality-wire equivalence: false/true is the literal I vertex with
native X edges; true/false is the literal X vertex with ordinary equality edges.
Each direction is an actual polynomial-time encoded oracle reduction. -/
theorem source_equality_wire_equivalence :
    Nonempty (Reduction G halg false true) ∧ Nonempty (Reduction G halg true false) :=
  ⟨⟨WireEquivalence.reduction (presentation G halg) (coordinates G halg) false true⟩,
    ⟨WireEquivalence.reduction (presentation G halg) (coordinates G halg) true false⟩⟩

/-- Literal resource-family correspondence, without changing or rescaling G. -/
theorem native_family :
    Set.range (fun i : Fin (s+1) =>
      (⟨targetArity s arity i.val,extendedSignatures G
        (fun _ : Fin 1 => Signature.equality) i⟩ : AnySignature L)) =
    Set.range (fun i : Fin s => (⟨arity i.val,G i⟩ : AnySignature L)) ∪
      {(⟨2,fun x => Signature.equality (x 0) (x 1)⟩ : AnySignature L)} :=
  extended_family G Signature.equality

theorem ordinary_family :
    Set.range (fun i : Fin (s+1) =>
      (⟨targetArity s arity i.val,extendedSignatures G
        (fun _ : Fin 1 => Signature.disequality) i⟩ : AnySignature L)) =
    Set.range (fun i : Fin s => (⟨arity i.val,G i⟩ : AnySignature L)) ∪
      {(⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ : AnySignature L)} :=
  extended_family G Signature.disequality

end
end Holant.Complexity.EdgeSubdivision.Source
