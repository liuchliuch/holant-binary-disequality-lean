import Holant.Proofs.Tractability.ProductMachine.CommonBasisSolver


namespace Holant.LocalDrafts.Tractability.ProductMachine.ProductClassSolver

open Computability Holant.Tractable Holant.Complexity Holant.Algebraic
open BinaryCompose FixedFieldMachines ProductElimination
open ExactSignatureTables Holant.Complexity.FixedGadgetSubstitution
noncomputable section

variable {s b : ℕ} {arity : ℕ → ℕ}
variable (signatures : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (kernels : Fin b → Kernel AlgebraicComplex)

def coefficients : CoefficientIndex s b arity → AlgebraicComplex
  | .inl ⟨i, x⟩ => signatures i x
  | .inr (i, x, y) => kernels i x y

theorem algebraic (a : CoefficientIndex s b arity) :
    IsAlgebraic ℚ (coefficients signatures kernels a) := Algebra.IsAlgebraic.isAlgebraic _

abbrev presentation := familyPresentation (coefficients signatures kernels) (algebraic signatures kernels)
abbrev tables := Holant.LocalDrafts.MainChain.CommonFieldTables.originalTables
  (coefficients signatures kernels) (algebraic signatures kernels)
abbrev value := (tables signatures kernels).evaluate (presentation signatures kernels)

theorem value_exact (r : Input s b arity) :
    (value signatures kernels r : AlgebraicComplex) =
      (r.val.realize r.property signatures kernels).denote Fin.elim0 := by
  simpa only [value, tables, coefficients, presentation,
    Holant.LocalDrafts.MainChain.CommonFieldTables.originalTables, id_eq] using
    PresentedScaledFamily.target_value_exact (coefficients signatures kernels)
      (algebraic signatures kernels) id r

variable (hv : ∀ i, Product (signatures i))
variable (he : ∀ i, Product (kernelSignature (kernels i)))

/-- The only inputs beyond the actual finite tables are source class-membership
proofs. `ofProduct` derives local formula proofs from the source definition. -/
def data : FamilyData s b arity where
  signatures := signatures
  kernels := kernels
  vertex i := ofProduct (hv i)
  edge i := ofProduct (he i)

def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (presentation signatures kernels).encoding (value signatures kernels) :=
  FamilyFieldSolver.computes (data signatures kernels hv he)

include hv he in
theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity)
    (presentation signatures kernels).encoding (value signatures kernels) :=
  (computes signatures kernels hv he).inFP

theorem primitive_bound (r : Input s b arity) :
    let w := computes signatures kernels hv he
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
      (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes signatures kernels hv he) r

section CommonEquality

variable (Gamma : SignatureFamily AlgebraicComplex)
variable (hsig : ∀ i, (⟨arity i.val, signatures i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
variable (h : CommonTransformable productClass Gamma)

def equalityData : CommonProductData s 1 arity :=
  commonEqualityData Gamma signatures hsig (Classical.choose h.2) (Classical.choose_spec h.2)

/-- One fixed shared basis and all fixed Product formulas are chosen before
the universal graph input. Equality edge labels remain the single original label. -/
def equalityComputes : Computes (RawClosedNetwork.validatedEncoding s 1 arity)
    (presentation signatures (fun _ : Fin 1 => Signature.equality)).encoding
    (value signatures (fun _ : Fin 1 => Signature.equality)) :=
  CommonBasisSolver.computes (equalityData signatures Gamma hsig h)

include Gamma hsig h in
theorem equality_inFP : InFP (RawClosedNetwork.validatedEncoding s 1 arity)
    (presentation signatures (fun _ : Fin 1 => Signature.equality)).encoding
    (value signatures (fun _ : Fin 1 => Signature.equality)) :=
  (equalityComputes signatures Gamma hsig h).inFP

end CommonEquality

section CommonDisequality

variable (Gamma : SignatureFamily AlgebraicComplex)
variable (hsig : ∀ i, (⟨arity i.val, signatures i⟩ : AnySignature AlgebraicComplex) ∈ Gamma)
variable (h : CommonKPresentationInKCoordinates productClass Gamma)

def disequalityData : CommonProductData s 1 arity :=
  commonKData Gamma signatures hsig (Classical.choose h.2) (Classical.choose_spec h.2)

/-- The native-X branch uses the original disequality edge kernel throughout;
no equality/disequality convention is changed by coefficient-field transport. -/
def disequalityComputes : Computes (RawClosedNetwork.validatedEncoding s 1 arity)
    (presentation signatures (fun _ : Fin 1 => Signature.disequality)).encoding
    (value signatures (fun _ : Fin 1 => Signature.disequality)) :=
  CommonBasisSolver.computes (disequalityData signatures Gamma hsig h)

include Gamma hsig h in
theorem disequality_inFP : InFP (RawClosedNetwork.validatedEncoding s 1 arity)
    (presentation signatures (fun _ : Fin 1 => Signature.disequality)).encoding
    (value signatures (fun _ : Fin 1 => Signature.disequality)) :=
  (disequalityComputes signatures Gamma hsig h).inFP

end CommonDisequality

end
end Holant.LocalDrafts.Tractability.ProductMachine.ProductClassSolver
