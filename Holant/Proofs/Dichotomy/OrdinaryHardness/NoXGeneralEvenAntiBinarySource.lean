import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenAntiFamily
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXScaleAux
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockTotal

/-! A bad binary and a full antidiagonal, each supplied as an actual even
private block, give an ordinary counted-verifier source. All four signed rows
are flattened into unchanged original labels before the oracle is queried. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiBinarySource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export OrdinaryNegativeMixedBlockData (family)
export OrdinaryNegativeSparseMixingSource (Block)
end D
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
namespace S
export NoXGeneralEvenAntiFamily (count signs privateCount rows balanced value)
end S
namespace T
export OrdinaryNegativeMixedBlockTotal (totalValue controlled)
end T
namespace B
export GeneralEOBinarySignedHardness (source rows pairings value)
export GeneralEOBinaryLiftOriginalField (complexRow)
end B
namespace Q
export GeneralEOSignedNativeQuery (count label signs)
end Q
namespace E
export StableHigherCurrentEvenCSPSource (tables)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {d s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K d) (H : (j : Fin s)→Signature K (a j.val))
variable (e p0 p1 : Fin s)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨a p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨a p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (row antiRow : D.Block (s:=s) (b:=a) 2) (v w : K)
variable (hv : v≠0) (hw : w≠0)
variable (anti : antiRow.signature H=NoXWeightedAntiSigned.anti v w)

def binary : Signature K 2 := fun z=>(v*w)^2*row.signature H z

include anti in
theorem value_exact : B.value K (binary K H row v w)=
    T.totalValue (M.trace H (S.privateCount row antiRow) (S.rows row antiRow)) := by
  funext r
  unfold B.value GeneralEOPairedFamilySigned.value GeneralEOPairedCSPFamilyNative.totalValue T.totalValue
  change (if r.WellFormed (arity:=fun _=>4) (D.family (Q.count (arity:=fun _=>4) B.pairings) (fun _=>2)) then _ else 0)=
    (if r.WellFormed (arity:=fun _=>4) (D.family (Q.count (arity:=fun _=>4) B.pairings) (fun _=>2)) then _ else 0)
  split_ifs
  · unfold GeneralEOPairedCSPFamilyRaw.value
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.prod_congr rfl
    intro j _
    let z : Fin 2→Bool := fun i=>GeneralEOPairedCSPRaw.read x
      (r.addresses.getD (r.offset (arity:=fun _=>4) (D.family _ (fun _=>2)) j.val+i.val) 0)
    have hs := GeneralEOPairedFamilySigned.signed_compressed (arity:=fun _=>4)
      (B.rows K (binary K H row v w)) B.pairings (Q.label (arity:=fun _=>4) B.pairings)
      (Q.signs (arity:=fun _=>4) B.pairings) (r.labelsFn j) z
    have hb (bits : Fin 2→Bool) : GeneralEOPairedCSPCycles.compress EOBinaryPlaneCore.pairing
        (EOBinaryPlaneCore.lift (binary K H row v w)) bits=binary K H row v w bits := by
      unfold GeneralEOPairedCSPCycles.compress
      rw [EOBinaryPlaneCore.pairing_word]
      exact congrFun (EOBinaryPlaneCore.compress_lift (binary K H row v w)) bits
    exact (hs.trans (hb _)).trans (S.value row antiRow H v w anti (r.labelsFn j) z).symm
  · rfl

def toOrdinary : LengthControlledOracleReduction
    (GeneralEOPairedCSPFamilyRaw.encoding (Q.count (arity:=fun _=>4) B.pairings)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    (B.value K (binary K H row v w)) ((E.tables F H).evaluate F) := by
  have h:=T.controlled F H e p0 p1 he h0 h1 (S.privateCount row antiRow)
    (S.rows row antiRow) (S.balanced row antiRow)
  rw [←value_exact K H row antiRow v w anti] at h
  exact h

variable (nonaffine : ¬Affine (B.complexRow K (row.signature H)))
variable (nonproduct : ¬Product (B.complexRow K (row.signature H)))

include hv hw nonaffine in
theorem scaled_nonaffine : ¬Affine (B.complexRow K (binary K H row v w)) := by
  have hn : ((v*w)^2 : K)≠0 := pow_ne_zero 2 (mul_ne_zero hv hw)
  exact NoXScaleAux.nonaffine_scale _ nonaffine _ (fun h=>hn (Subtype.ext h))

include hv hw nonproduct in
theorem scaled_nonproduct : ¬Product (B.complexRow K (binary K H row v w)) := by
  have hn : ((v*w)^2 : K)≠0 := pow_ne_zero 2 (mul_ne_zero hv hw)
  exact NoXScaleAux.nonproduct_scale _ nonproduct _ (fun h=>hn (Subtype.ext h))

variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (wit : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding count ((E.tables F H).evaluate F) :=
  Programme.compose (B.source K F (binary K H row v w)
      (scaled_nonaffine K H row v w hv hw nonaffine)
      (scaled_nonproduct K H row v w hv hw nonproduct) wit)
    (toOrdinary K F H e p0 p1 he h0 h1 row antiRow v w anti)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiBinarySource
end
