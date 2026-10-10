import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXScaleAux
import Holant.Proofs.Hardness.GeneralEOBinarySignedHardness

/-! An actual even non-Affine/non-Product binary and any actual full
weighted antidiagonal give a genuine counted-verifier ordinary source.
The paired sign guard contributes the same scalar to every signed row;
the binary hardness theorem is applied to that exact scaled binary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiBinarySource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe family)
end D
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
namespace S
export NoXWeightedAntiSigned (recipe even_recipe trace_value)
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
variable {d s k : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K d) (H : (j : Fin s)→Signature K (a j.val))
variable (e p0 p1 antiLabel : Fin s)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨a p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨a p1.val,H p1⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (left right : K)
variable (hl : left≠0) (hr : right≠0)
variable (ha : (⟨a antiLabel.val,H antiLabel⟩ : AnySignature K)=⟨2,NoXWeightedAntiSigned.anti left right⟩)
variable (blocks : D.Recipe (u:=1) (s:=s) (a:=fun _=>2+k) (b:=a))
variable (balanced : D.EvenRecipe blocks)

def binary : Signature K 2 := fun z=>(left*right)^2*M.trace H k blocks 0 z
abbrev pairings : (i : Fin 1)→OrientedPerfectPairing ((fun _ : ℕ=>4) i.val) := B.pairings
abbrev signs : Fin (Q.count (arity:=fun _=>4) pairings)→Fin 2→Bool :=
  Q.signs (arity:=fun _=>4) pairings

def signedBlocks := S.recipe blocks (signs) antiLabel (congrArg Sigma.fst ha)

include balanced in
theorem signed_even : D.EvenRecipe (signedBlocks K H antiLabel left right ha blocks) :=
  S.even_recipe blocks (signs) antiLabel (congrArg Sigma.fst ha) balanced

include ha in
theorem value_exact : B.value K (binary K H left right blocks)=
    T.totalValue (M.trace H (2+k) (signedBlocks K H antiLabel left right ha blocks)) := by
  funext r
  unfold B.value GeneralEOPairedFamilySigned.value GeneralEOPairedCSPFamilyNative.totalValue
  unfold T.totalValue
  change (if r.WellFormed (arity:=fun _=>4) (D.family (Q.count (arity:=fun _=>4) pairings) (fun _=>2)) then _ else 0)=
    (if r.WellFormed (arity:=fun _=>4) (D.family (Q.count (arity:=fun _=>4) pairings) (fun _=>2)) then _ else 0)
  split_ifs
  · unfold GeneralEOPairedCSPFamilyRaw.value
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.prod_congr rfl
    intro v _
    let z : Fin 2→Bool := fun j=>GeneralEOPairedCSPRaw.read x
      (r.addresses.getD (r.offset (arity:=fun _=>4) (D.family _ (fun _=>2)) v.val+j.val) 0)
    have hs := GeneralEOPairedFamilySigned.signed_compressed (arity:=fun _=>4)
      (B.rows K (binary K H left right blocks)) pairings (Q.label (arity:=fun _=>4) pairings)
      (Q.signs (arity:=fun _=>4) pairings) (r.labelsFn v) z
    have hb (w : Fin 2→Bool) : GeneralEOPairedCSPCycles.compress EOBinaryPlaneCore.pairing
        (EOBinaryPlaneCore.lift (binary K H left right blocks)) w=binary K H left right blocks w := by
      unfold GeneralEOPairedCSPCycles.compress
      rw [EOBinaryPlaneCore.pairing_word]
      exact congrFun (EOBinaryPlaneCore.compress_lift (binary K H left right blocks)) w
    exact (hs.trans (hb _)).trans
      (S.trace_value blocks signs antiLabel H left right ha (r.labelsFn v) z).symm
  · rfl

def toOrdinary : LengthControlledOracleReduction
    (GeneralEOPairedCSPFamilyRaw.encoding (Q.count (arity:=fun _=>4) pairings)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    (B.value K (binary K H left right blocks)) ((E.tables F H).evaluate F) := by
  have h := T.controlled F H e p0 p1 he h0 h1 (2+k)
    (signedBlocks K H antiLabel left right ha blocks) (signed_even K H antiLabel left right ha blocks balanced)
  rw [←value_exact K H antiLabel left right ha blocks] at h
  exact h

variable (nonaffine : ¬Affine (B.complexRow K (M.trace H k blocks 0)))
variable (nonproduct : ¬Product (B.complexRow K (M.trace H k blocks 0)))

include nonaffine hl hr in
theorem scaled_nonaffine : ¬Affine (B.complexRow K (binary K H left right blocks)) := by
  have hn : ((left*right)^2 : K)≠0 := pow_ne_zero 2 (mul_ne_zero hl hr)
  have hc : (((left*right)^2 : K) : AlgebraicComplex)≠0 := fun h=>hn (Subtype.ext h)
  exact NoXScaleAux.nonaffine_scale _ nonaffine _ hc

include nonproduct hl hr in
theorem scaled_nonproduct : ¬Product (B.complexRow K (binary K H left right blocks)) := by
  have hn : ((left*right)^2 : K)≠0 := pow_ne_zero 2 (mul_ne_zero hl hr)
  have hc : (((left*right)^2 : K) : AlgebraicComplex)≠0 := fun h=>hn (Subtype.ext h)
  exact NoXScaleAux.nonproduct_scale _ nonproduct _ hc

variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding count ((E.tables F H).evaluate F) :=
  Programme.compose (B.source K F (binary K H left right blocks)
      (scaled_nonaffine K H left right hl hr blocks nonaffine)
      (scaled_nonproduct K H left right hl hr blocks nonproduct) w)
    (toOrdinary K F H e p0 p1 antiLabel he h0 h1 left right ha blocks balanced)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiBinarySource
end
