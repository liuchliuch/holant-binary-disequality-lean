import Holant.Proofs.Hardness.GeneralEOAffinePlanePeriod
import Holant.Proofs.Hardness.GeneralEOAffinePlaneChain
import Holant.Proofs.Hardness.GeneralEONonARSPinningFieldBridge
import Holant.Proofs.Hardness.GeneralEOSinglePinSource

/-! A generic mapped-binary period lemma in a fixed original subfield, followed
by its application to an actual labelled native-X network. The scalar is
4096 times the 24th power of the compressed 00 entry. No extension is needed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkField
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue)
end O
namespace B
export EOBinaryPlaneCore (compress lift)
end B
namespace C
export GeneralEOAffinePlaneChain (table Mat)
end C
namespace P
export GeneralEOAffinePlanePeriod (table scale power scale_ne_zero)
end P
namespace L
export GeneralEONonARSPinningFieldBridge (lift labels exact native denote_lift)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Mapped
variable (S : IntermediateField ℚ AlgebraicComplex) (f : Signature S 2)
variable (g : Signature AlgebraicComplex 2) (hm : ∀x,(f x : AlgebraicComplex)=g x)

def scale : S := 4096*(f ![false,false])^24

include hm in
theorem scale_value : (scale S f : AlgebraicComplex)=P.scale g := by
  change S.subtype (4096*(f ![false,false])^24)=_
  simp only [map_mul,map_pow,map_ofNat]
  rw [show S.subtype (f ![false,false])=g ![false,false] from hm _]
  rfl

include hm in
theorem mapped_table : (C.table f).map S.subtype=P.table g := by
  apply Matrix.ext
  intro i k
  fin_cases i <;> fin_cases k <;> exact hm _

include hm in
theorem scale_nonzero (hf : EOBinaryPlaneClassification.Full g) : scale S f≠0 := by
  intro hz
  have h := scale_value S f g hm
  rw [hz] at h
  exact P.scale_ne_zero g hf h.symm

include hm in
theorem power (hf : EOBinaryPlaneClassification.Full g) (hA : Affine g) (hP : ¬Product g) :
    C.table f^24=scale S f • (1 : C.Mat (K:=S)) := by
  have h := P.power g hf hA hP
  have hmap : (C.table f^24).map S.subtype=(P.table g)^24 := by
    calc
      _ = ((C.table f).map S.subtype)^24 := Matrix.map_pow _ S.subtype 24
      _ = _ := congrArg (fun z=>z^24) (mapped_table S f g hm)
  apply Matrix.ext
  intro i k
  apply Subtype.ext
  have hv := congrFun (congrFun hmap i) k
  change ((C.table f^24) i k : AlgebraicComplex)=_ at hv
  rw [h] at hv
  rw [hv]
  simp only [Matrix.smul_apply,smul_eq_mul]
  change P.scale g*(1 : Matrix (Fin 2) (Fin 2) AlgebraicComplex) i k=
    S.subtype (scale S f*(1 : C.Mat (K:=S)) i k)
  rw [map_mul,show S.subtype (scale S f)=P.scale g from scale_value S f g hm]
  congr 1
  simp only [Matrix.one_apply]
  split_ifs <;> rfl
end Mapped

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable (N : Network AlgebraicComplex 4) (NL : Labelling N.shape s 1 a)
variable (hN : LabelledNetwork.Exact G N NL) (hn : ∀i,N.edge i=Signature.disequality)
variable (e : Equiv.Perm (Fin 4))

abbrev lifted := L.lift G N NL
abbrev labels := L.labels G N NL

def binary : Signature (O.originalField G) 2 := B.compress (Tensor.reindex e (lifted G N NL).denote)
def ambient : Signature AlgebraicComplex 2 := B.compress (Tensor.reindex e N.denote)
abbrev scale := Mapped.scale (O.originalField G) (binary G N NL e)

include hN hn in
theorem binary_value (x : Fin 2→Bool) :
    (binary G N NL e x : AlgebraicComplex)=ambient N e x :=
  L.denote_lift G N NL hN hn _

include hN hn in
theorem scale_value : (scale G N NL e : AlgebraicComplex)=P.scale (ambient N e) :=
  Mapped.scale_value _ _ _ (binary_value G N NL hN hn e)

include hN hn in
theorem original_plane
    (hplane : Tensor.reindex e N.denote=B.lift (ambient N e)) :
    Tensor.reindex e (lifted G N NL).denote=B.lift (binary G N NL e) := by
  funext x
  apply Subtype.ext
  change ((lifted G N NL).denote (fun k=>x (e k)) : AlgebraicComplex)=_
  rw [L.denote_lift G N NL hN hn]
  have h := congrFun hplane x
  change N.denote (fun k=>x (e k))=B.lift (ambient N e) x at h
  rw [h]
  unfold B.lift
  split_ifs
  · exact (binary_value G N NL hN hn e _).symm
  · rfl

include hN hn in
theorem scale_nonzero (hf : EOBinaryPlaneClassification.Full (ambient N e)) : scale G N NL e≠0 :=
  Mapped.scale_nonzero _ _ _ (binary_value G N NL hN hn e) hf

include hN hn in
theorem power (hf : EOBinaryPlaneClassification.Full (ambient N e))
    (hA : Affine (ambient N e)) (hP : ¬Product (ambient N e)) :
    C.table (binary G N NL e)^24=scale G N NL e • (1 : C.Mat (K:=O.originalField G)) :=
  Mapped.power _ _ _ (binary_value G N NL hN hn e) hf hA hP

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkField
