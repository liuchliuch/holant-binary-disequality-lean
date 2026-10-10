import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.RootSearchDriver.Height


namespace Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.RootSearchDriver
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.Tractability.AffineMachine CertificateMachine

def cross {A B : Type*} (xs : List A) (ys : List B) : List (A × B) :=
  xs.flatMap (fun a => ys.map (fun b => (a,b)))
@[simp] theorem mem_cross {A B : Type*} {a : A} {b : B} {xs : List A} {ys : List B} :
    (a,b) ∈ cross xs ys ↔ a ∈ xs ∧ b ∈ ys := by
  simp [cross]

def fraction (x : ℕ × ℕ) : ℚ := mkRat (Equiv.intEquivNat.symm x.1) (x.2+1)
def rationals (n : ℕ) : List ℚ := (cross (List.range n) (List.range n)).map fraction
def wires (qs : List ℚ) : List CertificateWire :=
  cross (cross qs qs) (cross (cross qs qs) (cross qs qs))
def certificates (h : ℕ) : List Certificate :=
  (wires (rationals (Height.cutoff h))).map certificateUnwire

theorem rational_mem {q : ℚ} {n : ℕ}
    (hn : Equiv.intEquivNat q.num < n) (hd : q.den ≤ n) : q ∈ rationals n := by
  have hdpos := q.den_pos
  apply List.mem_map.mpr
  refine ⟨(Equiv.intEquivNat q.num,q.den-1), ?_, ?_⟩
  · exact mem_cross.mpr ⟨List.mem_range.mpr hn, List.mem_range.mpr (by omega)⟩
  · have hd' : q.den-1+1=q.den := by omega
    simp [fraction,hd']

theorem rational_mem_of_length (q : ℚ) (h : ℕ)
    (hq : (rationalEncoding.encode q).length ≤ h) : q ∈ rationals (Height.cutoff h) := by
  have hs : Nat.size (rationalCode q) ≤ h := by
    simpa only [rationalEncoding,encodeNat_length] using hq
  have hb : rationalCode q < Height.cutoff h :=
    ((Nat.lt_size_self (rationalCode q)).trans_le
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hs)).trans_le (Height.pow_le_cutoff h)
  exact rational_mem ((Nat.left_le_pair _ _).trans_lt hb)
    ((Nat.right_le_pair _ _).trans (Nat.le_of_lt hb))

/-- Coverage uses the ACTUAL certificate wire length, not an Encodable index.
The family may also contain longer codes; no equality of height conventions
with rawThrough is asserted. -/
theorem certificate_mem (t : Certificate) (h : ℕ)
    (ht : (certificateEncoding.encode t).length ≤ h) : t ∈ certificates h := by
  have hl := certificate_length t
  have hc₁ := rational_mem_of_length t.center.1 h (by omega)
  have hc₂ := rational_mem_of_length t.center.2 h (by omega)
  have hb₁ := rational_mem_of_length t.inverseSlope.1 h (by omega)
  have hb₂ := rational_mem_of_length t.inverseSlope.2 h (by omega)
  have hr := rational_mem_of_length t.radius h (by omega)
  have hm := rational_mem_of_length t.magnitude h (by omega)
  apply List.mem_map.mpr
  refine ⟨certificateWire t, ?_, certificateUnwire_wire t⟩
  change ((t.center.1,t.center.2),(t.inverseSlope.1,t.inverseSlope.2),t.radius,t.magnitude) ∈
    wires (rationals (Height.cutoff h))
  simp only [certificateWire,wires,mem_cross]
  exact ⟨⟨hc₁,hc₂⟩,⟨⟨hb₁,hb₂⟩,⟨hr,hm⟩⟩⟩

theorem canonical_generated (h : ℕ) (t : Certificate) (_ht : t ∈ certificates h) :
    certificateEncoding.decode (certificateEncoding.encode t) = some t :=
  certificateEncoding.decode_encode t

theorem certificate_word_mem (t : Certificate) (h : ℕ)
    (ht : (certificateEncoding.encode t).length ≤ h) :
    certificateEncoding.encode t ∈ (certificates h).map certificateEncoding.encode :=
  List.mem_map.mpr ⟨t,certificate_mem t h ht,rfl⟩

noncomputable section

/-- Physical contextual map followed by physical flatten. The nesting is a
fixed product constructor, but BOTH lists are unbounded runtime inputs. -/
def crossComputes {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool) :
    Computes (pairEncoding (framedListEncoding ea) (framedListEncoding eb))
      (framedListEncoding (pairEncoding ea eb)) (fun x => cross x.1 x.2) := by
  let input := pairEncoding (framedListEncoding ea) (framedListEncoding eb)
  let cellInput := pairEncoding input ea
  let context := Wiring.firstComputes input ea
  let a := Wiring.secondComputes input ea
  let ys := context.andThen (Wiring.secondComputes (framedListEncoding ea) (framedListEncoding eb))
  let cell : Computes cellInput (framedListEncoding (pairEncoding ea eb))
      (fun x => x.1.2.map (fun b => (x.2,b))) :=
    (pairComputes a ys).andThen
      (mapListComputes ea eb (pairEncoding ea eb) (fun a b => (a,b))
        (identityComputes (pairEncoding ea eb)))
  let outer := AccessPrograms.map ea (framedListEncoding (pairEncoding ea eb))
    (Wiring.firstComputes (framedListEncoding ea) (framedListEncoding eb))
    (fun x a => x.2.map (fun b => (a,b))) cell
  exact congrComputes (outer.andThen (WireLists.flatten (pairEncoding ea eb)))
    (fun x => by simp only [Function.comp_apply,cross,List.flatMap_def])

/-- The signed-natural and integer codecs have literally identical words.
Integer sign interpretation is subsequently executed by normalizationForward.
This recoding has no decoder call and does not change machine instructions. -/
def signedCodeComputes : Computes encodingNatBool IntegerArithmetic.encoding Equiv.intEquivNat.symm :=
  recode (identityComputes encodingNatBool) id (fun _ => rfl)
    (fun n => by simp [encodingNatBool,IntegerArithmetic.encoding])

def fractionComputes : Computes Height.tailEncoding rationalEncoding fraction :=
  (pairComputes
    (((Wiring.firstComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding).andThen
      UnaryBinary.computes).andThen signedCodeComputes)
    (((Wiring.secondComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding).andThen
      WireLists.succComputes).andThen UnaryBinary.computes)).andThen
        RationalArithmetic.normalizationForwardComputes

def rationalsComputes : Computes UnaryBinary.unaryEncoding (framedListEncoding rationalEncoding) rationals :=
  ((pairComputes ComponentSelection.UnaryRange.computes ComponentSelection.UnaryRange.computes).andThen
    (crossComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)).andThen
      (WireLists.mapComputes Height.tailEncoding rationalEncoding fraction fractionComputes)

def wiresComputes : Computes (framedListEncoding rationalEncoding)
    (framedListEncoding certificateWireEncoding) wires := by
  let scalarList := identityComputes (framedListEncoding rationalEncoding)
  let pairs := (pairComputes scalarList scalarList).andThen (crossComputes rationalEncoding rationalEncoding)
  let tail := (pairComputes pairs pairs).andThen (crossComputes CertificateMachine.gaussianEncoding CertificateMachine.gaussianEncoding)
  exact (pairComputes pairs tail).andThen
    (crossComputes CertificateMachine.gaussianEncoding
      (pairEncoding CertificateMachine.gaussianEncoding CertificateMachine.gaussianEncoding))

def unwireComputes : Computes certificateWireEncoding certificateEncoding certificateUnwire :=
  recode (identityComputes certificateWireEncoding) id (fun _ => rfl)
    (fun w => by simp only [id_eq,certificateEncoding,certificateWire_unwire])

def generationComputes : FiniteComputes encodingNatBool (framedListEncoding certificateEncoding) certificates :=
  ((Height.computes.andThen (FiniteComputes.ofPoly rationalsComputes)).andThen
    (FiniteComputes.ofPoly wiresComputes)).andThen
      (FiniteComputes.ofPoly (WireLists.mapComputes certificateWireEncoding certificateEncoding
        certificateUnwire unwireComputes))

def generationTimed : Turing.TM2ComputableInTime encodingNatBool.encode
    (framedListEncoding certificateEncoding).encode certificates := generationComputes.toTM2ComputableInTime

end
end Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.RootSearchDriver
