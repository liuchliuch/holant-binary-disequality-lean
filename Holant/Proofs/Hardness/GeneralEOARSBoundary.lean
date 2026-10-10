import Holant.Proofs.Hardness.ComplexConjugatePinObstruction

/-! The genuine ARS-up-to-scalars residual is kept separate from global
pinning. Unequal complementary norms exclude that residual for the selected
original row. No converse, universal pinning split, or hardness is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSBoundary
open Holant
namespace R
export ComplexConjugatePinObstruction (ConjugateReversal)
end R
namespace F
export SelfDualPinObstruction (flip oriented01)
end F
set_option backward.isDefEq.respectTransparency false

def ARSUpToScale {n : ℕ} (f : Signature ℂ n) : Prop :=
  ∃c : ℂ,c≠0 ∧ ∃g : Signature ℂ n,R.ConjugateReversal g ∧ f=c • g

def FamilyARS {s : ℕ} {a : ℕ→ℕ} (G : (i : Fin s)→Signature ℂ (a i.val)) : Prop :=
  ∀i,ARSUpToScale (G i)

theorem opposite_norm {n : ℕ} (f : Signature ℂ n) (hf : ARSUpToScale f)
    (x : Fin n→Bool) : ‖f (F.flip x)‖=‖f x‖ := by
  obtain ⟨c,_,g,hg,rfl⟩ := hf
  change ‖c*g (F.flip x)‖=‖c*g x‖
  rw [hg x,norm_mul,norm_mul]
  simp

theorem binary_equal_norm (f : Signature ℂ 2) (hf : ARSUpToScale f) :
    ‖f ![false,true]‖=‖f ![true,false]‖ := by
  have h := opposite_norm f hf ![false,true]
  have hflip : F.flip ![false,true]=(![true,false] : Fin 2→Bool) := by
    funext i
    fin_cases i <;> rfl
  rw [hflip] at h
  exact h.symm

theorem unequal_binary_not_ARS (f : Signature ℂ 2)
    (hn : ‖f ![false,true]‖≠‖f ![true,false]‖) : ¬ARSUpToScale f :=
  fun hf=>hn (binary_equal_norm f hf)

theorem selected_binary_not_family {s : ℕ} {a : ℕ→ℕ}
    (G : (i : Fin s)→Signature ℂ (a i.val)) (M : Signature ℂ 2) (j : Fin s)
    (hj : (⟨a j.val,G j⟩ : AnySignature ℂ)=⟨2,M⟩)
    (hn : ‖M ![false,true]‖≠‖M ![true,false]‖) : ¬FamilyARS G := by
  intro hf
  apply unequal_binary_not_ARS M hn
  exact (congrArg (fun f : AnySignature ℂ=>ARSUpToScale f.2) hj).mp (hf j)

/-- A local obstruction says nothing about global oracle interpolation. -/
theorem no_nonzero_pin (f : Signature ℂ 2) (hf : ARSUpToScale f) (c : ℂ) (hc : c≠0) :
    f≠c • F.oriented01 := by
  intro h
  have he := binary_equal_norm f hf
  rw [h] at he
  have hz : ‖c‖=0 := by simpa [F.oriented01,Pi.smul_apply,smul_eq_mul] using he
  exact hc (norm_eq_zero.mp hz)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSBoundary
