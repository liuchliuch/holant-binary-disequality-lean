import Holant.Proofs.Hardness.GeneralEOSinglePinDEQInclusion
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Platonic.PhysicalCostComposition

/-! Same-field installation of an arbitrary actual scalar macro. In the DEQ4
case the literal pin inclusion, three-query anchor programme, physical macro
replacement and occurrence-count scalar correction are composed directly.
The macro can be any original-labelled native graph; there is no affine-plane
or matrix-power hypothesis and no adjoined coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryMacro
open Computability Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open UniversalPairReduction
namespace P
export GeneralEOSinglePinAmplificationProgramme (inputEncoding sourceValue source)
end P
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {d s n : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
abbrev G := ValueJoins.signatures F T
variable (N : Network K n) (NL : Labelling N.shape s 1 a)
abbrev g := NL.template
abbrev valid := NL.wellFormed
abbrev arity := sourceArity (Adjoin.templates s a (g N NL))
variable (c : K)
abbrev coordinates := ScaledAdjoin.coordinates F T (g N NL) (valid N NL) c
abbrev tables := sourceTables (Adjoin.templates s a (g N NL)) T (coordinates F T N NL c)
abbrev signatures := G F (tables F T N NL c)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (arity N NL)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev sourceValue := (tables F T N NL c).evaluate F

variable (hn : ∀i b b',F.decode (T.edge i b b')=Signature.disequality b b')
variable (hN : LabelledNetwork.Exact (G F T) N NL)
variable (hNative : ∀i,N.edge i=Signature.disequality)

omit [Field K] [Algebra ℚ K] [CharZero K] in
private theorem apply_exact {m k : ℕ} (f : Signature K m) (g : Signature K k)
    (h : (⟨m,f⟩ : AnySignature K)=⟨k,g⟩) (hk : m=k) (x : Fin k → Bool) :
    f (fun i => x (Fin.cast hk i))=g x := by
  cases h
  rfl

omit [CharZero K] in
include hn hN hNative in
theorem macro_actual :
    ((g N NL).network (valid N NL) (G F T)
      (fun i b b' => F.decode (T.edge i b b'))).denote=N.denote := by
  apply Labelling.denote_template_of_labels NL (G F T)
    (fun i b b' => F.decode (T.edge i b b')) N.vertex N.edge
  · intro v x
    exact apply_exact _ _ (hN v) (NL.vertex_arity v) x
  · intro e b b'
    change F.decode (T.edge (NL.edge e) b b')=N.edge e b b'
    exact (hn (NL.edge e) b b').trans (congrFun₂ (hNative e).symm b b')

private def decodeAny (z : AnySignature (Fin d → ℚ)) : AnySignature K :=
  ⟨z.1,fun x => F.decode (z.2 x)⟩

omit [CharZero K] in
theorem old_signature (i : Fin s) :
    (⟨arity N NL i.val,signatures F T N NL c i.castSucc⟩ : AnySignature K)=
      ⟨a i.val,G F T i⟩ := by
  have he : (⟨arity N NL i.val,coordinates F T N NL c i.castSucc⟩ : AnySignature (Fin d → ℚ))=
      ⟨a i.val,T.vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (g N NL) i)
      (ScaledAdjoin.old_coordinates F T (g N NL) (valid N NL) c i)
  exact congrArg (decodeAny F) he

omit [CharZero K] in
include hn hN hNative in
theorem new_signature (hc : c≠0) (H : Signature K n) (hH : N.denote=c • H) :
    (⟨arity N NL s,signatures F T N NL c ⟨s,Nat.lt_succ_self s⟩⟩ : AnySignature K)=⟨n,H⟩ := by
  have he : (⟨arity N NL s,coordinates F T N NL c ⟨s,Nat.lt_succ_self s⟩⟩ :
      AnySignature (Fin d → ℚ))=
      ⟨n,fun x => F.decode.symm (((g N NL).network (valid N NL) (G F T)
        (fun i b b' => F.decode (T.edge i b b'))).denote x/c)⟩ :=
    Sigma.ext (Adjoin.new_boundary (g N NL))
      (ScaledAdjoin.new_coordinates F T (g N NL) (valid N NL) c)
  refine (congrArg (decodeAny F) he).trans ?_
  change (⟨n,fun x => F.decode (F.decode.symm
    (((g N NL).network (valid N NL) (G F T)
      (fun i b b' => F.decode (T.edge i b b'))).denote x/c))⟩ : AnySignature K)=_
  congr 1
  funext x
  rw [LinearEquiv.apply_symm_apply,macro_actual F T N NL hn hN hNative,hH]
  exact mul_div_cancel_left₀ (H x) hc

omit [CharZero K] in
include hn in
theorem native_tables : ∀i b b',F.decode ((tables F T N NL c).edge i b b')=
    Signature.disequality b b' := hn

omit [CharZero K] in
include hn in
theorem source_value_eq : sourceValue F T N NL c=
    (fun q => (q.val.realize q.property (signatures F T N NL c)
      (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0) := by
  funext q
  rw [sourceValue,ExactSignatureTables.evaluate_eq_decoded]
  have he : (fun i b b' => F.decode ((tables F T N NL c).edge i b b'))=
      (fun _ : Fin 1 => Signature.disequality) := by
    funext i b b'
    exact native_tables F T N NL c hn i b b'
  rw [he]

def remove (hc : c≠0) : LengthControlledOracleReduction (inputEncoding N NL) F.encoding
    (targetEncoding (s:=s) (a:=a)) F.encoding (sourceValue F T N NL c) (T.evaluate F) :=
  Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin F T (g N NL) (valid N NL) c hc

section DEQ
variable (Q : Network K 4) (QL : Labelling Q.shape s 1 a)
variable (hQ : LabelledNetwork.Exact (G F T) Q QL)
variable (hQNative : ∀i,Q.edge i=Signature.disequality)
variable (hc : c≠0) (hE : Q.denote=c • ExactTwoSignatures.E)

def withDEQ : LengthControlledOracleReduction
    (P.inputEncoding (s:=s+1) (a:=arity Q QL)) F.encoding
    (targetEncoding (s:=s) (a:=a)) F.encoding
    (P.sourceValue F (tables F T Q QL c)) (T.evaluate F) :=
  C.composeControlled
    (P.source F (tables F T Q QL c) (native_tables F T Q QL c hn)
      ⟨s,Nat.lt_succ_self s⟩
      (new_signature F T Q QL c hn hQ hQNative hc ExactTwoSignatures.E hE))
    (remove F T Q QL c hc)

/-- The input has only original rows and arbitrary directed01 occurrences;
every DEQ vertex introduced internally is expanded into the supplied actual
original-labelled graph, with its exact nonzero field scalar corrected. -/
def deqSource : LengthControlledOracleReduction
    (P.inputEncoding (s:=s) (a:=a)) F.encoding
    (targetEncoding (s:=s) (a:=a)) F.encoding (P.sourceValue F T) (T.evaluate F) :=
  C.composeControlled
    (GeneralEOSinglePinDEQInclusion.source F T (signatures F T Q QL c)
      (old_signature F T Q QL c))
    (withDEQ F T c hn Q QL hQ hQNative hc hE)
end DEQ

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryMacro
