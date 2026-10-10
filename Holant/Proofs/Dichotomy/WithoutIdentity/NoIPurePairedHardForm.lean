import Holant.Tractable.Criteria
import Mathlib.Tactic

/-! The fixed interleaved opposite-pair lift. Its canonical pairing recovers
exactly the logical row, so the class choice in EOTract is genuinely shared
by all rows, including rows of different logical arities. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHardForm
open Holant Holant.Tractable
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false

def pairing (m : ℕ) : OrientedPerfectPairing (m*2) where
  count:=m
  ports:=(Equiv.prodCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans finProdFinEquiv

def compatible {m : ℕ} (z : Fin (m*2)→Bool) : Prop:=
  ∀j : Fin m,z (finProdFinEquiv (j,(1 : Fin 2)))= !(z (finProdFinEquiv (j,(0 : Fin 2))))

instance compatibleDecidable {m : ℕ} (z : Fin (m*2)→Bool) : Decidable (compatible z) := by
  unfold compatible
  infer_instance

def paired {K : Type} [Zero K] {m : ℕ} (h : Signature K m) : Signature K (m*2):=fun z=>
  if compatible z then h (fun j=>z (finProdFinEquiv (j,(0 : Fin 2)))) else 0

@[simp] theorem word_zero {m : ℕ} (z : Fin m→Bool) (j : Fin m) :
    (pairing m).word z (finProdFinEquiv (j,(0 : Fin 2)))=z j := by
  simp [pairing,OrientedPerfectPairing.word,finTwoEquiv]

@[simp] theorem word_one {m : ℕ} (z : Fin m→Bool) (j : Fin m) :
    (pairing m).word z (finProdFinEquiv (j,(1 : Fin 2)))= !(z j) := by
  simp [pairing,OrientedPerfectPairing.word,finTwoEquiv]

@[simp] theorem paired_word {K : Type} [Zero K] {m : ℕ}
    (h : Signature K m) (z : Fin m→Bool) : paired h ((pairing m).word z)=h z := by
  have good : compatible ((pairing m).word z):=fun j=>by simp
  simp [paired,good]

@[simp] theorem restrict_paired {m : ℕ} (h : Signature AlgebraicComplex m) :
    (pairing m).restrict (paired h)=h := by
  funext z
  exact paired_word h z

theorem weight_compatible {m : ℕ} (z : Fin (m*2)→Bool) (good : compatible z) : weight z=m := by
  unfold weight
  rw [←finProdFinEquiv.sum_comp,Fintype.sum_prod_type]
  have each (j : Fin m) : (∑k : Fin 2,if z (finProdFinEquiv (j,k)) then 1 else 0)=1 := by
    rw [Fin.sum_univ_two,good j]
    cases z (finProdFinEquiv (j,(0 : Fin 2))) <;> rfl
  simp only [each,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

theorem central {K : Type} [CommSemiring K] {m : ℕ} (h : Signature K m) :
    Signature.CentralSupport (paired h) := by
  intro z bad
  unfold paired
  split_ifs with good
  · exact False.elim (bad (by rw [weight_compatible z good];omega))
  · rfl

theorem nonzero {K : Type} [Zero K] {m : ℕ} {h : Signature K m} (nz : h≠0) : paired h≠0 := by
  intro zero
  apply nz
  funext z
  have e:=congrFun zero ((pairing m).word z)
  simpa only [paired_word,Pi.zero_apply] using e

theorem affine_nullary (h : Signature AlgebraicComplex 0) : Affine h := by
  have e:h=(fun _=>h Fin.elim0):=funext (fun z=>congrArg h (Subsingleton.elim _ _))
  rw [e]
  exact affine_constant 0 _

theorem product_nullary (h : Signature AlgebraicComplex 0) : Product h := by
  have e:h=(fun _=>h Fin.elim0):=funext (fun z=>congrArg h (Subsingleton.elim _ _))
  rw [e]
  exact product_constant 0 _

theorem positive_of_nonaffine {m : ℕ} {h : Signature AlgebraicComplex m} (bad : ¬Affine h) : 0<m := by
  cases m with
  | zero=>exact False.elim (bad (affine_nullary h))
  | succ m=>omega

theorem positive_of_nonproduct {m : ℕ} {h : Signature AlgebraicComplex m} (bad : ¬Product h) : 0<m := by
  cases m with
  | zero=>exact False.elim (bad (product_nullary h))
  | succ m=>omega

theorem nonzero_of_nonaffine {m : ℕ} {h : Signature AlgebraicComplex m} (bad : ¬Affine h) : h≠0 := by
  rintro rfl
  exact bad (affine_zero m)

theorem nonzero_of_nonproduct {m : ℕ} {h : Signature AlgebraicComplex m} (bad : ¬Product h) : h≠0 := by
  rintro rfl
  exact bad (product_zero m)

/-- One actual fixed pairing is enough to exclude either family-wide class. -/
theorem not_tract {m n : ℕ} (h : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (badA : ¬Affine h) (badP : ¬Product g) :
    ¬EOTract (preprocess {⟨m*2,paired h⟩,⟨n*2,paired g⟩}) := by
  intro tract
  obtain ⟨_,_,sign,C,_,classes⟩:=tract
  have hmem : (⟨m*2,paired h⟩ : AnySignature AlgebraicComplex)∈
      preprocess {⟨m*2,paired h⟩,⟨n*2,paired g⟩}:=
    ⟨Set.mem_insert _ _,Nat.mul_pos (positive_of_nonaffine badA) (by omega),
      nonzero (nonzero_of_nonaffine badA)⟩
  have gmem : (⟨n*2,paired g⟩ : AnySignature AlgebraicComplex)∈
      preprocess {⟨m*2,paired h⟩,⟨n*2,paired g⟩}:=
    ⟨Set.mem_insert_of_mem _ (Set.mem_singleton _),Nat.mul_pos (positive_of_nonproduct badP) (by omega),
      nonzero (nonzero_of_nonproduct badP)⟩
  cases C with
  | affine=>exact badA (by simpa [EOClass.Holds] using classes _ hmem (pairing m))
  | product=>exact badP (by simpa [EOClass.Holds] using classes _ gmem (pairing n))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHardForm
end
