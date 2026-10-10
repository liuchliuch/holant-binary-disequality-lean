import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalMergePhase

/-! A supported bad local-twist cube survives an actual pair merge whenever
its eight corners and marker obey that same coordinate relation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalMergeFailure
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.AffinePatching
namespace M
export NoXLocalMergePhase (equal unequal opposite equal_of_local opposite_of_local)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r n : ℕ}

theorem ratio_agree (f g : Signature AlgebraicComplex r) (z u v w : Word r)
    (same : ∀j : Fin 8,f (cubeWords z u v w j)=g (cubeWords z u v w j)) :
    thirdRatio f z u v w=thirdRatio g z u v w := by
  let c := cubeWords z u v w
  change (f (c 7)*f (c 1)*f (c 2)*f (c 3))/(f (c 4)*f (c 5)*f (c 6)*f (c 0))=
    (g (c 7)*g (c 1)*g (c 2)*g (c 3))/(g (c 4)*g (c 5)*g (c 6)*g (c 0))
  simp only [c,same]

variable (f : Signature AlgebraicComplex (n+2)) (e : Word r→Word (n+2))
variable (affine : TwoTranslate.IsAffineMap e) (a : Word (n+2))
variable (supported : f a≠0) (z u v w : Word r)
variable (full : ∀j : Fin 8,f (e (cubeWords z u v w j))≠0)
variable (bad : thirdRatio (fun x=>localTwist a f (e x)) z u v w≠1)
include affine supported full bad in
theorem equal_notLocal (marker : a 0=a 1)
    (corners : ∀j : Fin 8,e (cubeWords z u v w j) 0=e (cubeWords z u v w j) 1) :
    ¬LocalAffine (M.equal f) := by
  intro localg
  have hg := (M.equal_of_local f a supported marker localg).precompose e affine
  have same (j : Fin 8) : M.equal (localTwist a f) (e (cubeWords z u v w j))=
      localTwist a f (e (cubeWords z u v w j)) := by
    exact ite_eq_left (corners j)
  have nonzero (j : Fin 8) : M.equal (localTwist a f) (e (cubeWords z u v w j))≠0 := by
    rw [same]
    exact (NoXLocalRankOneCriterion.twist_support f a _).mpr (full j)
  have hc := affine_supported_cube _ hg z u v w nonzero
  exact bad ((ratio_agree _ _ z u v w same).symm.trans hc)

include affine supported full bad in
theorem opposite_notLocal (b c : AlgebraicComplex) (hb : b≠0) (hc : c≠0)
    (fourth : b^4= -(c^4)) (marker : a 0≠a 1)
    (corners : ∀j : Fin 8,e (cubeWords z u v w j) 0≠e (cubeWords z u v w j) 1) :
    ¬LocalAffine (M.opposite f b c) := by
  intro localg
  have hg := (M.opposite_of_local f a b c hb hc fourth supported marker localg).precompose e affine
  have same (j : Fin 8) : M.unequal (localTwist a f) (e (cubeWords z u v w j))=
      localTwist a f (e (cubeWords z u v w j)) := by
    exact ite_eq_left (corners j)
  have nonzero (j : Fin 8) : M.unequal (localTwist a f) (e (cubeWords z u v w j))≠0 := by
    rw [same]
    exact (NoXLocalRankOneCriterion.twist_support f a _).mpr (full j)
  have cube := affine_supported_cube _ hg z u v w nonzero
  exact bad ((ratio_agree _ _ z u v w same).symm.trans cube)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalMergeFailure
end
