import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleCore
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseOccurrences

/-! Literal original-port normalization of a signed two-bundle pinning.
All live original coordinates remain separate. The sixteen emitted rows have
even incidence at every free and constant port. Only a semantic restriction
uses the bundle signs, to prove that the actual block is non-Product. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleNormalize
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace S
export OrdinaryNegativeNonproductBundleSupport (Face signedWord product_signed_substitute)
end S
namespace C
export OrdinaryNegativeNonproductBundleCore (scale first second character normalize_octic scale_ne_zero)
end C
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate evaluate_append evaluate_replicate)
end B
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace O
export GeneralEOPairedFamilyExtractionPhaseOccurrences (rawPorts occurrences count_ofFn)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ} {f : Signature AlgebraicComplex n}

/-- Original coordinate i is either literally exposed as i or literally
pinned. There is no negation gate and no identification of signed ports. -/
def mask (D : S.Face f) (keep : Fin 2→Bool) : Fin n→Bool ⊕ Fin n := fun i=>
  match D.ports i with
  | .inl b => .inl (D.base i ^^ b)
  | .inr j => if keep j then .inr i else .inl (D.base i)

def rows (D : S.Face f) : List (Fin n→Bool ⊕ Fin n) :=
  [mask D ![true,true]]++List.replicate 7 (mask D ![true,false])++
    List.replicate 7 (mask D ![false,true])++[mask D ![false,false]]

theorem rows_length (D : S.Face f) : (rows D).length=16 := by simp [rows]

def coefficient (D : S.Face f) : Signature AlgebraicComplex n := B.evaluate f (rows D)

theorem substitute_mask (D : S.Face f) (keep : Fin 2→Bool) (z : Fin 2→Bool) :
    T.substitute (mask D keep) (S.signedWord D.base D.ports z)=
      S.signedWord D.base D.ports (fun j=>keep j && z j) := by
  funext i
  cases hp : D.ports i with
  | inl b => simp [mask,T.substitute,S.signedWord,OrdinaryNegativeNonproductBundleSupport.flip,hp]
  | inr j => cases hk : keep j <;>
      simp [mask,T.substitute,S.signedWord,OrdinaryNegativeNonproductBundleSupport.flip,hp,hk]

theorem restricted_value (D : S.Face f) (z : Fin 2→Bool) :
    coefficient D (S.signedWord D.base D.ports z)=
      OrdinaryNegativeNonproductBundleCore.normalize D z*C.scale D := by
  simp only [coefficient,rows,B.evaluate_append,B.evaluate_replicate]
  have hsingle (k : Fin 2→Bool) :
      B.evaluate f [mask D k] (S.signedWord D.base D.ports z)=D.binary (fun j=>k j && z j) := by
    simp only [B.evaluate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,substitute_mask]
    rfl
  rw [hsingle,hsingle]
  simp only [substitute_mask]
  have h11 : (fun j=>(![true,true] : Fin 2→Bool) j && z j)=z := by
    funext j; fin_cases j <;> simp
  have h10 : (fun j=>(![true,false] : Fin 2→Bool) j && z j)=![z 0,false] := by
    funext j; fin_cases j <;> simp
  have h01 : (fun j=>(![false,true] : Fin 2→Bool) j && z j)=![false,z 1] := by
    funext j; fin_cases j <;> simp
  have h00 : (fun j=>(![false,false] : Fin 2→Bool) j && z j)=![false,false] := by
    funext j; fin_cases j <;> simp
  change D.binary _*D.binary _^7*D.binary _^7*D.binary _=_
  rw [h11,h10,h01,h00]
  rfl

theorem octic_value (D : S.Face f) (h1 : C.first D^8=1) (h2 : C.second D^8=1)
    (z : Fin 2→Bool) :
    coefficient D (S.signedWord D.base D.ports z)=C.scale D^16*C.character (z 0) (z 1) := by
  rw [restricted_value,C.normalize_octic D h1 h2]
  ring

theorem octic_nonproduct (D : S.Face f) (h1 : C.first D^8=1) (h2 : C.second D^8=1) :
    ¬Product (coefficient D) := by
  intro hp
  have hs := S.product_signed_substitute D.base D.ports hp
  have hf : EOBinaryPlaneClassification.Full (fun z=>coefficient D (S.signedWord D.base D.ports z)) := by
    intro z
    dsimp only
    rw [octic_value D h1 h2]
    apply mul_ne_zero (pow_ne_zero _ (C.scale_ne_zero D))
    cases z 0 <;> cases z 1 <;> norm_num [C.character]
  have hc := (EOBinaryPlaneClassification.full_product_iff _ hf).mp hs
  unfold EOBinaryPlaneClassification.Cross at hc
  simp only [octic_value D h1 h2] at hc
  norm_num [C.character] at hc
  have hz : C.scale D=0 := by
    have hh : C.scale D^32=0 := by linear_combination -hc/2
    exact (pow_eq_zero_iff (by decide)).mp hh
  exact C.scale_ne_zero D hz

/-- No eighth-root hypothesis is needed to retain non-Product interaction.
The normalization only raises the two nonzero unary weights to eighth powers. -/
theorem nonproduct (D : S.Face f) : ¬Product (coefficient D) := by
  intro hp
  have hs := S.product_signed_substitute D.base D.ports hp
  have hv (z : Fin 2→Bool) :
      coefficient D (S.signedWord D.base D.ports z)=C.scale D^16*
        (if z 0 then C.first D^8 else 1)*(if z 1 then C.second D^8 else 1)*C.character (z 0) (z 1) := by
    rw [restricted_value,OrdinaryNegativeNonproductBundleCore.normalize_formula]
    ring
  have hf : EOBinaryPlaneClassification.Full (fun z=>coefficient D (S.signedWord D.base D.ports z)) := by
    intro z
    dsimp only
    rw [restricted_value]
    unfold OrdinaryNegativeNonproductBundleCore.normalize
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (D.full z) (pow_ne_zero _ (D.full _)))
      (pow_ne_zero _ (D.full _))) (C.scale_ne_zero D)
  have hc := (EOBinaryPlaneClassification.full_product_iff _ hf).mp hs
  unfold EOBinaryPlaneClassification.Cross at hc
  simp only [hv] at hc
  norm_num [C.character] at hc
  have hz : 2*C.scale D^32*C.first D^8*C.second D^8=0 := by linear_combination -hc
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (C.scale_ne_zero D)))
    (pow_ne_zero _ (OrdinaryNegativeNonproductBundleCore.first_ne_zero D)))
    (pow_ne_zero _ (OrdinaryNegativeNonproductBundleCore.second_ne_zero D))) hz

def coordinateCount (D : S.Face f) (q : Bool ⊕ Fin n) (i : Fin n) : ℕ :=
  (if mask D ![true,true] i=q then 1 else 0)+
    7*(if mask D ![true,false] i=q then 1 else 0)+
    7*(if mask D ![false,true] i=q then 1 else 0)+
    (if mask D ![false,false] i=q then 1 else 0)

theorem coordinate_even (D : S.Face f) (q : Bool ⊕ Fin n) (i : Fin n) :
    Even (coordinateCount D q i) := by
  cases hp : D.ports i with
  | inl b => simp only [coordinateCount,mask,hp]; split_ifs <;> decide
  | inr j =>
    fin_cases j
    all_goals simp [coordinateCount,mask,hp]
    all_goals split_ifs <;> norm_num at *

theorem count_eq (D : S.Face f) (q : Bool ⊕ Fin n) :
    (O.rawPorts (rows D)).count q=∑i,coordinateCount D q i := by
  simp only [O.rawPorts,List.count_flatMap,Function.comp_def,rows,List.map_append,List.sum_append,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.map_replicate,List.sum_replicate,
    O.count_ofFn,add_zero,coordinateCount,Finset.sum_add_distrib,nsmul_eq_mul,Finset.mul_sum]
  norm_num

theorem even_ports (D : S.Face f) (q : Bool ⊕ Fin n) : Even ((O.rawPorts (rows D)).count q) := by
  rw [count_eq,even_iff_two_dvd]
  exact Finset.dvd_sum (fun i _=>(even_iff_two_dvd.mp (coordinate_even D q i)))

/-- Actual per-variable incidence, including unused original coordinates. -/
theorem even_occurrences (D : S.Face f) (i : Fin n) : Even (O.occurrences (rows D) i) :=
  even_ports D (.inr i)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleNormalize
end
