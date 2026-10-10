import Holant.Complexity.UniversalPairReduction.Reduction
import Holant.Complexity.EdgeSubdivision.WireFamily

/-! Source Lemma 3.2 for every fixed finite algebraic signature family. The
coefficient field is derived from Gamma itself; the actual input keeps its
original labelled rows, ordered incidences, loops, parallel edges and nullary
vertices. The sole promise is at most one ordered Delta occurrence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction.Source
open Computability Holant.Algebraic FixedGadgetSubstitution
variable {L : Type} [Field L] [Algebra ℚ L]
local instance ambientCharZero : CharZero L := Algebra.charZero_of_charZero ℚ L
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature L (arity i.val))
variable (halg : ∀i x,IsAlgebraic ℚ (G i x))

abbrev field := FiniteFamily.field G
local instance fieldAlgebra : Algebra ℚ (field G) := (FiniteFamily.field G).algebra'
abbrev presentation := FiniteFamily.presentation G halg
abbrev tables := FiniteFamily.tables G halg
abbrev sourceValue := BinaryFamily.value
  (ValueJoins.signatures (presentation G halg) (tables G halg)) BinaryTable.delta
abbrev targetValue := (tables G halg).evaluate (presentation G halg)

 theorem native_tables : ∀i a b,
    (presentation G halg).decode ((tables G halg).edge i a b)=Signature.disequality a b := by
  intro i a b
  apply Subtype.val_injective
  have h := familyCoordinates_spec (FiniteFamily.coefficient G)
    (FiniteFamily.coefficient_algebraic G halg) (.inr (i,a,b))
  change _ = (Signature.disequality (K:=field G) a b : L)
  apply Eq.trans h
  cases a <;> cases b <;> rfl

/-- The target is the unchanged native-X Holant problem over the original Gamma. -/
theorem target_value_exact (r : ExactSignatureTables.Input s 1 arity) :
    ((targetValue G halg r : field G) : L) =
      (r.val.realize r.property G (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 :=
  FiniteFamily.target_exact G halg r

/-- The source answer is exactly the original one-Delta assignment sum, not a
surrogate signature or an alternative encoding of a preprocessed instance. -/
theorem source_value_exact (r : Input s arity) :
    ((sourceValue G halg r : field G) : L) =
      (r.val.realize r.property.1 (BinaryFamily.signatures G BinaryTable.delta)
        (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 := by
  unfold sourceValue BinaryFamily.value
  change (field G).subtype _ = _
  rw [←Network.denote_map (field G).subtype]
  congr 1
  unfold BinaryFamily.network Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    dsimp only
    unfold BinaryFamily.signatures
    split_ifs with hi
    · exact familyCoordinates_spec (FiniteFamily.coefficient G)
        (FiniteFamily.coefficient_algebraic G halg) _
    · change ((BinaryTable.delta _ _ : field G) : L)=BinaryTable.delta _ _
      simp only [BinaryTable.delta]
      split_ifs <;> rfl
  · funext e a b
    cases a <;> cases b <;> rfl

/-- The finite source labels denote precisely Gamma together with the literal
ordered delta0 tensor delta1. This includes coincident labels and empty Gamma. -/
theorem source_family_exact :
    Set.range (fun i : Fin (s+1) =>
      (⟨extendedArity s arity i.val,BinaryFamily.signatures G BinaryTable.delta i⟩ : AnySignature L)) =
    Set.range (fun i : Fin s => (⟨arity i.val,G i⟩ : AnySignature L)) ∪
      {(⟨2,fun x => BinaryTable.delta (x 0) (x 1)⟩ : AnySignature L)} :=
  EdgeSubdivision.extended_family G BinaryTable.delta

abbrev Reduction := RepresentedReduction (presentation G halg) (tables G halg)

/-- Source Lemma 3.2: a real polynomial-time Boolean-stack oracle reduction
from native-X Holant(Gamma,Delta≤1) to native-X Holant(Gamma), making at most
three actual oracle calls. No EO, parity, charge or tractability premise. -/
theorem source_universal_one_pair_reduction :
    ∃r : Reduction G halg,ThreeQuery.AtMostQueries r.machine 3 :=
  represented_one_pair_reduction (presentation G halg) (tables G halg) (native_tables G halg)

 theorem source_universal_one_pair_reducible : OracleReducible
    (inputEncoding s arity) (presentation G halg).encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) (presentation G halg).encoding
    (sourceValue G halg) (targetValue G halg) := by
  obtain ⟨r,_⟩ := source_universal_one_pair_reduction G halg
  exact ⟨r⟩

/-- At-most-one validation changes no byte of the original raw graph encoding. -/
theorem source_input_exact (r : Input s arity) :
    (inputEncoding s arity).encode r=RawClosedNetwork.encoding.encode r.val := rfl

end Holant.Complexity.UniversalPairReduction.Source
