import Holant.Tractable.SourceCorrespondence
import Holant.EOCompletion
import Holant.TensorAction

/-!
# The seven-clause criterion and its four-clause binary reduction

Literal structural predicates from authoritative `paper1.tex` (rewritten
2026-09-27), definitions `def:eo-tract`, `def:tract-X`, and the seven alternatives
in `subsec:tract-predicate`. These definitions assert neither algorithms nor
complexity bounds. Public criteria first delete zero and nullary signatures.
-/

namespace Holant.Tractable
noncomputable section

/-- Delete precisely the zero and arity-zero signatures, before classification. -/
def preprocess (F : SignatureFamily AlgebraicComplex) : SignatureFamily AlgebraicComplex :=
  {f | f ∈ F ∧ 0 < f.1 ∧ f.2 ≠ 0}

/-- The domain convention used for the displayed source criteria. -/
def Preprocessed (F : SignatureFamily AlgebraicComplex) : Prop :=
  ∀ f ∈ F, 0 < f.1 ∧ f.2 ≠ 0

@[simp] theorem mem_preprocess (F : SignatureFamily AlgebraicComplex)
    (f : AnySignature AlgebraicComplex) :
    f ∈ preprocess F ↔ f ∈ F ∧ 0 < f.1 ∧ f.2 ≠ 0 := Iff.rfl

theorem preprocess_preprocessed (F : SignatureFamily AlgebraicComplex) :
    Preprocessed (preprocess F) := fun _ h => h.2

theorem preprocess_eq_self {F : SignatureFamily AlgebraicComplex} (h : Preprocessed F) :
    preprocess F = F := Set.ext (fun f => ⟨fun hf => hf.1, fun hf => ⟨hf, h f hf⟩⟩)

@[simp] theorem preprocess_idempotent (F : SignatureFamily AlgebraicComplex) :
    preprocess (preprocess F) = preprocess F := preprocess_eq_self (preprocess_preprocessed F)

/-- A uniform, whole-signature image, with one matrix shared by the entire family. -/
def familyAction (B : InvertibleKernel) (F : SignatureFamily AlgebraicComplex) :
    SignatureFamily AlgebraicComplex :=
  (fun f : AnySignature AlgebraicComplex => ⟨f.1, B.action f.2⟩) '' F

/-- The fixed source K-coordinate image; inverse K acts at every port. -/
def kCoordinates (F : SignatureFamily AlgebraicComplex) : SignatureFamily AlgebraicComplex :=
  familyAction sourceKBasis.symm F

/-- An ordered, oriented perfect pairing. `false` is the first incidence and
`true` the second incidence of each pair; the equivalence partitions all ports. -/
structure OrientedPerfectPairing (n : ℕ) where
  count : ℕ
  ports : (Fin count × Bool) ≃ Fin n

/-- The unique opposite-bit word for a pairing and its compressed assignment. -/
def OrientedPerfectPairing.word {n : ℕ} (p : OrientedPerfectPairing n)
    (z : Fin p.count → Bool) : Fin n → Bool := fun j =>
  let q := p.ports.symm j
  if q.2 then !(z q.1) else z q.1

/-- The source's compressed opposite-pair restriction `g^π`, retaining values. -/
def OrientedPerfectPairing.restrict {n : ℕ} (p : OrientedPerfectPairing n)
    (g : Signature AlgebraicComplex n) : Signature AlgebraicComplex p.count :=
  fun z => g (p.word z)

/-- The single family-wide choice of one of the two source classes. -/
inductive EOClass where
  | affine
  | product

def EOClass.Holds (C : EOClass) {n : ℕ} (g : Signature AlgebraicComplex n) : Prop :=
  match C with
  | .affine => Affine g
  | .product => Product g

/-- A sign has precisely the two permitted integer values. -/
inductive EOSign where
  | positive
  | negative

def EOSign.value : EOSign → ℤ
  | .positive => 1
  | .negative => -1

/-- Three-way addition in the Boolean cube, in the original ordered ports. -/
def tripleXor {n : ℕ} (a b c : Fin n → Bool) : Fin n → Bool :=
  fun j => Bool.xor (Bool.xor (a j) (b j)) (c j)

/-- EO means even arity and central support. -/
def IsEO (g : AnySignature AlgebraicComplex) : Prop :=
  (∃ d, g.1 = 2 * d) ∧ Signature.CentralSupport g.2

/-- Exactly one sign and one A/P class are chosen outside both family universals.
The initial conjuncts record the source's finite-EO-family domain. -/
def EOTract (G : SignatureFamily AlgebraicComplex) : Prop :=
  G.Finite ∧ (∀ g ∈ G, IsEO g) ∧ ∃ sign : EOSign, ∃ C : EOClass,
    (∀ g ∈ G, ∀ a b c, g.2 a ≠ 0 → g.2 b ≠ 0 → g.2 c ≠ 0 →
      g.2 (tripleXor a b c) ≠ 0 ∨ 0 < sign.value * Holant.charge (tripleXor a b c)) ∧
    (∀ g ∈ G, ∀ p : OrientedPerfectPairing g.1, C.Holds (p.restrict g.2))

@[simp] theorem eoTract_empty : EOTract ∅ := by
  refine ⟨Set.finite_empty, ?_, EOSign.positive, EOClass.affine, ?_, ?_⟩
  all_goals intro g hg; exact False.elim hg

/-- Zero central restrictions, including every odd-arity restriction, are deleted. -/
def centralFamily (G : SignatureFamily AlgebraicComplex) : SignatureFamily AlgebraicComplex :=
  {h | ∃ g ∈ G, Signature.centralRestriction g.2 ≠ 0 ∧
    h = ⟨g.1, Signature.centralRestriction g.2⟩}

/-- The literal ordered completion, with original ports before the added pins.
Nonzero single-layer members determine their layer uniquely. -/
def completionFamily (G : SignatureFamily AlgebraicComplex) : SignatureFamily AlgebraicComplex :=
  {h | ∃ g ∈ G, g.2 ≠ 0 ∧ ∃ d, Signature.SingleLayer g.2 d ∧
    h = Signature.completeToEO g.2 d}

/-- All support charges have the same weak sign, shared by the family. -/
def CommonOneSided (G : SignatureFamily AlgebraicComplex) : Prop :=
  (∀ g ∈ G, ∀ x, g.2 x ≠ 0 → 0 ≤ Holant.charge x) ∨
  (∀ g ∈ G, ∀ x, g.2 x ≠ 0 → Holant.charge x ≤ 0)

/-- Both strict charge signs must actually occur in support, across the family. -/
def BothChargeSigns (G : SignatureFamily AlgebraicComplex) : Prop :=
  (∃ g ∈ G, ∃ x, g.2 x ≠ 0 ∧ Holant.charge x < 0) ∧
  (∃ g ∈ G, ∃ x, g.2 x ≠ 0 ∧ 0 < Holant.charge x)

/-- Source clause (1), including its EO condition. -/
def OneSidedAlternative (F : SignatureFamily AlgebraicComplex) : Prop :=
  CommonOneSided (kCoordinates F) ∧ EOTract (centralFamily (kCoordinates F))

/-- Source clause (2), including both charge signs and the completion EO condition. -/
def SingleWeightAlternative (F : SignatureFamily AlgebraicComplex) : Prop :=
  (∀ g ∈ kCoordinates F, ∃ d, Signature.SingleLayer g.2 d) ∧
  BothChargeSigns (kCoordinates F) ∧ EOTract (completionFamily (kCoordinates F))

/-- The source convention additionally puts zero in every tensor closure.
The nonzero branch is an actual finite disjoint ordered tensor decomposition. -/
def SourceTensorClosure (C : (n : ℕ) → Signature AlgebraicComplex n → Prop)
    {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  f = 0 ∨ Signature.TensorClosure C f

/-- T consists of unary and binary signatures. -/
def ArityTwoAlternative (F : SignatureFamily AlgebraicComplex) : Prop :=
  ∀ f ∈ F, SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) f.2

/-- Actual tensorwise K or KX image of M, rather than an abstract membership oracle. -/
def matchingImage (opposite : Bool) (n : ℕ) (f : Signature AlgebraicComplex n) : Prop :=
  ∃ g : Signature AlgebraicComplex n, AtMostOneSupport g ∧
    Signature.coordinateAction
      (fun _ => if opposite then Kernel.mul KMatrix Signature.disequality else KMatrix) g = f

/-- Source clause (4): the orientation is common to the entire family. -/
def MatchingAlternative (F : SignatureFamily AlgebraicComplex) : Prop :=
  (∀ f ∈ F, SourceTensorClosure (matchingImage false) f.2) ∨
  (∀ f ∈ F, SourceTensorClosure (matchingImage true) f.2)

/-- All seven source alternatives on a preprocessed finite family. -/
def TractCore (F : SignatureFamily AlgebraicComplex) : Prop :=
  OneSidedAlternative F ∨ SingleWeightAlternative F ∨ ArityTwoAlternative F ∨
  MatchingAlternative F ∨ CommonTransformable affineClass F ∨
  CommonTransformable productClass F ∨ CommonTransformable localAffineClass F

/-- Exactly source clauses (3), (5), (6), (7), with the same shared-basis predicates. -/
def TractXCore (F : SignatureFamily AlgebraicComplex) : Prop :=
  ArityTwoAlternative F ∨ CommonTransformable affineClass F ∨
  CommonTransformable productClass F ∨ CommonTransformable localAffineClass F

/-- The public full criterion first performs the prescribed deletion step. -/
def Tract (F : SignatureFamily AlgebraicComplex) : Prop :=
  (preprocess F).Finite ∧ TractCore (preprocess F)

/-- The public reduced criterion uses the identical deletion step. -/
def TractX (F : SignatureFamily AlgebraicComplex) : Prop :=
  (preprocess F).Finite ∧ TractXCore (preprocess F)

theorem TractXCore.tractCore {F : SignatureFamily AlgebraicComplex}
    (h : TractXCore F) : TractCore F := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem TractX.tract {F : SignatureFamily AlgebraicComplex} (h : TractX F) : Tract F :=
  ⟨h.1, h.2.tractCore⟩

end
end Holant.Tractable
