import Holant.Proofs.Tractability.ProductMachine.FamilyCatalogue
import Holant.Proofs.Tractability.ProductMachine.RawFamily
import Holant.Proofs.Algorithms.CommonFieldTables


namespace Holant.LocalDrafts.Tractability.ProductMachine.FamilyFieldSolver

open Computability Holant.Tractable Holant.Complexity Holant.Algebraic
open BinaryCompose FixedFieldMachines ProductElimination
open Holant.Complexity.ExactSignatureTables
open Holant.Complexity.FixedGadgetSubstitution
noncomputable section

variable {s b : ℕ} {arity : ℕ → ℕ} (D : FamilyData s b arity)

def originalCoefficient : CoefficientIndex s b arity → AlgebraicComplex
  | .inl ⟨i, x⟩ => D.signatures i x
  | .inr (i, x, y) => D.kernels i x y

theorem original_algebraic (a : CoefficientIndex s b arity) :
    IsAlgebraic ℚ (originalCoefficient D a) := Algebra.IsAlgebraic.isAlgebraic _

theorem extra_algebraic (a : FamilyCatalogue.Slot D) :
    IsAlgebraic ℚ (FamilyCatalogue.extra D a) := Algebra.IsAlgebraic.isAlgebraic _

abbrev combined := Holant.LocalDrafts.MainChain.FamilyFieldInclusion.combined
  (originalCoefficient D) (FamilyCatalogue.extra D)

theorem combined_algebraic (a : CoefficientIndex s b arity ⊕ FamilyCatalogue.Slot D) :
    IsAlgebraic ℚ (combined D a) :=
  Holant.LocalDrafts.MainChain.FamilyFieldInclusion.combined_algebraic
    (originalCoefficient D) (FamilyCatalogue.extra D) (original_algebraic D) (extra_algebraic D) a

abbrev originalPresentation := familyPresentation (originalCoefficient D) (original_algebraic D)
abbrev commonPresentation := familyPresentation (combined D) (combined_algebraic D)
abbrev embedding := Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding
  (originalCoefficient D) (FamilyCatalogue.extra D)

abbrev originalTables := Holant.LocalDrafts.MainChain.CommonFieldTables.originalTables
  (originalCoefficient D) (original_algebraic D)
abbrev commonTables := Holant.LocalDrafts.MainChain.CommonFieldTables.commonTables
  (originalCoefficient D) (FamilyCatalogue.extra D) (original_algebraic D) (extra_algebraic D)

/-- The rational table used by the actual literal interpreter. The index
equivalence is compile-time finite data, not a runtime graph-numbering oracle. -/
def coordinates (a : Fin (FamilyCatalogue.labelCount D)) :
    Fin (Module.finrank ℚ (familyField (combined D))) → ℚ :=
  familyCoordinates (combined D) (combined_algebraic D) (.inr ((FamilyCatalogue.labels D).symm a))

theorem decoded_coefficient (a : Fin (FamilyCatalogue.labelCount D)) :
    ((commonPresentation D).decode (coordinates D a) : AlgebraicComplex) =
      FamilyCatalogue.coefficient D a :=
  familyCoordinates_spec (combined D) (combined_algebraic D) _

/-- Membership of each original and each decomposition coefficient in this
specific common field is proved by the actual finite generating family. -/
theorem original_mem (a : CoefficientIndex s b arity) :
    originalCoefficient D a ∈ familyField (combined D) :=
  coefficient_mem_familyField (combined D) (.inl a)

theorem decomposition_mem (a : FamilyCatalogue.Slot D) :
    FamilyCatalogue.extra D a ∈ familyField (combined D) :=
  coefficient_mem_familyField (combined D) (.inr a)

def commonSignatures (i : Fin s) : Signature (familyField (combined D)) (arity i.val) :=
  fun x => (commonPresentation D).decode ((commonTables D).vertex i x)

def commonKernels (i : Fin b) : Kernel (familyField (combined D)) :=
  fun x y => (commonPresentation D).decode ((commonTables D).edge i x y)

@[simp] theorem commonSignature_value (i : Fin s) (x : Fin (arity i.val) → Bool) :
    (commonSignatures D i x : AlgebraicComplex) = D.signatures i x :=
  familyCoordinates_spec (combined D) (combined_algebraic D) (.inl (.inl ⟨i, x⟩))

@[simp] theorem commonKernel_value (i : Fin b) (x y : Bool) :
    (commonKernels D i x y : AlgebraicComplex) = D.kernels i x y :=
  familyCoordinates_spec (combined D) (combined_algebraic D) (.inl (.inr (i, x, y)))

/-- Derived, never supplied: the very templates collected from D satisfy the
local tensor equations in the generated common field. -/
theorem localFormulas :
    RawFamily.LocalFormulas (FamilyCatalogue.labelCount D) s b arity
      (FamilyCatalogue.vertices D) (FamilyCatalogue.edges D)
      (commonPresentation D) (coordinates D) (commonSignatures D) (commonKernels D) := by
  let φ : familyField (combined D) →+* AlgebraicComplex :=
    (familyField (combined D)).val.toRingHom
  have hc : (fun a => φ ((commonPresentation D).decode (coordinates D a))) =
      FamilyCatalogue.coefficient D := by
    funext a
    exact decoded_coefficient D a
  constructor
  · intro i x
    apply φ.injective
    have hl : φ (ProductElimination.weight ((FamilyCatalogue.vertices D i).map
        (LabelledFactor.realize (FieldInterpreter.coefficients (commonPresentation D) (coordinates D)))) x) =
        D.signatures i x := by
      rw [← weight_map]
      simpa only [List.map_map, Function.comp_def, realize_map, FieldInterpreter.coefficients,
        hc] using FamilyCatalogue.vertex_formula D i x
    exact hl.trans (commonSignature_value D i x).symm
  · intro i x
    apply φ.injective
    have hl : φ (ProductElimination.weight ((FamilyCatalogue.edges D i).map
        (LabelledFactor.realize (FieldInterpreter.coefficients (commonPresentation D) (coordinates D)))) x) =
        D.kernels i (x 0) (x 1) := by
      rw [← weight_map]
      simpa only [List.map_map, Function.comp_def, realize_map, FieldInterpreter.coefficients,
        hc] using FamilyCatalogue.edge_formula D i x
    exact hl.trans (commonKernel_value D i (x 0) (x 1)).symm

abbrev commonValue := (commonTables D).evaluate (commonPresentation D)
abbrev originalValue := (originalTables D).evaluate (originalPresentation D)

/-- Instantiate all data and all local equations of RawFamily from D itself. -/
def commonComputes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (commonPresentation D).encoding (commonValue D) :=
  RawFamily.holantComputes (FamilyCatalogue.labelCount D) s b arity
    (FamilyCatalogue.vertices D) (FamilyCatalogue.edges D)
    (commonPresentation D) (coordinates D) (commonSignatures D) (commonKernels D) (localFormulas D)

theorem commonValue_embedding (r : Input s b arity) :
    commonValue D r = embedding D (originalValue D r) :=
  Holant.LocalDrafts.MainChain.CommonFieldTables.value_embedding
    (originalCoefficient D) (FamilyCatalogue.extra D) (original_algebraic D) (extra_algebraic D) r

/-- The enlargement caused by a Product decomposition is removed from the
answer interface by the existing concrete MainChain codec machine. -/
def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (originalPresentation D).encoding (originalValue D) :=
  congrComputes ((commonComputes D).andThen
    (Holant.LocalDrafts.MainChain.FamilyFieldInclusion.recoverComputes
      (originalCoefficient D) (FamilyCatalogue.extra D) (original_algebraic D) (extra_algebraic D)))
    (fun r => by
      dsimp only [Function.comp_def]
      rw [commonValue_embedding]
      exact Holant.LocalDrafts.MainChain.FamilyFieldInclusion.recover_embed
        (originalCoefficient D) (FamilyCatalogue.extra D) (originalValue D r))

theorem originalValue_exact (r : Input s b arity) :
    (originalValue D r : AlgebraicComplex) = (D.network r).denote Fin.elim0 := by
  simpa only [originalValue, originalTables, originalCoefficient, FamilyData.network,
    Holant.LocalDrafts.MainChain.CommonFieldTables.originalTables, originalPresentation, id_eq] using
    PresentedScaledFamily.target_value_exact (originalCoefficient D) (original_algebraic D) id r

/-- Compatibility with the old arithmetic evaluator is a derived value theorem.
Its semantic Fintype numbering is not used by the new machine's port compiler. -/
theorem originalValue_evaluate (r : Input s b arity) :
    (originalValue D r : AlgebraicComplex) = D.evaluate r := by
  rw [originalValue_exact, FamilyData.evaluate_exact]

theorem commonValue_ambient (r : Input s b arity) :
    (commonValue D r : AlgebraicComplex) = D.evaluate r := by
  calc
    _ = ((embedding D (originalValue D r)) : AlgebraicComplex) :=
      congrArg (fun x : familyField (combined D) => (x : AlgebraicComplex)) (commonValue_embedding D r)
    _ = (originalValue D r : AlgebraicComplex) :=
      Holant.LocalDrafts.MainChain.FamilyFieldInclusion.embedding_value _ _ _
    _ = _ := originalValue_evaluate D r

theorem primitive_bound (r : Input s b arity) :
    let w := computes D
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
      (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes D) r

def answerBits (r : Input s b arity) : List Bool :=
  (originalPresentation D).encoding.encode (originalValue D r)

theorem answerBits_decode (r : Input s b arity) :
    (originalPresentation D).encoding.decode (answerBits D r) = some (originalValue D r) :=
  (originalPresentation D).encoding.decode_encode _

end
end Holant.LocalDrafts.Tractability.ProductMachine.FamilyFieldSolver
