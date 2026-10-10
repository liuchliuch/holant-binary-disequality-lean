import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralRanks

/-! Coefficient extraction from the preserved marked-octahedral proof. An arbitrary full-rank map preserving the SAME
24 marked root directions produces a literal permutation and nonzero
image multipliers. No candidate list or incidence-completeness premise is
used. The inverse is the inverse of this map, not a newly selected map.
The similarities below are coefficient proofs, never physical vertices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open scoped BigOperators Matrix

/-- These are the existing marked representatives in their existing order. -/
theorem point_projectively_injective (f : Form) (i j : Fin 24) (c : ℂ)
    (h : point f i = c • point f j) : i = j := by
  have hc : c ≠ 0 := by
    intro hz
    exact point_ne_zero f i (by simpa only [hz,zero_smul] using h)
  have he : kernel f i=c • kernel f j := by
    apply coordinates.injective
    simpa only [map_smul,point] using h
  have hp := congrArg (complexPull f) he
  simp only [kernel,complexMatrix_theta,complexPull_smul,complexPull_complexTheta] at hp
  apply RainbowOrbit.projectively_injective .octahedral i j c
  change RainbowOrbit.goldenMatrix (RainbowOrbit.octahedralRaw i)=
    c • RainbowOrbit.goldenMatrix (RainbowOrbit.octahedralRaw j)
  simpa only [RainbowOrbit.octahedralRaw_standard] using hp

/-- A receipt for the actual linear operator, with its actual image scales. -/
structure RootAction (f : Form) (A : End) where
  perm : Equiv.Perm (Fin 24)
  scale : Fin 24 → ℂ
  scale_ne_zero : ∀ i, scale i ≠ 0
  image_eq : ∀ i, A *ᵥ point f i = scale i • point f (perm i)

theorem rootAction_exists (f : Form) (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots f) A) :
    ∃ σ : Equiv.Perm (Fin 24), ∃ c : Fin 24 → ℂ,
      (∀ i, c i ≠ 0) ∧ ∀ i, A *ᵥ point f i = c i • point f (σ i) := by
  have hi := Matrix.mulVec_injective_of_det_ne_zero hd
  have images (i : Fin 24) : ∃ j : Fin 24, ∃ c : ℂ,
      c ≠ 0 ∧ A *ᵥ point f i = c • point f j := by
    rcases h _ (point_mem f i) with hz | hm
    · apply False.elim
      apply point_ne_zero f i
      exact hi (by simpa only [Matrix.mulVec_zero] using hz)
    · exact (roots_iff f _).mp hm
  choose σ c hc he using images
  have hs : Function.Injective σ := by
    intro i j hij
    have hh : A *ᵥ point f i = (c i * (c j)⁻¹) • (A *ᵥ point f j) := by
      rw [he i,he j,hij,smul_smul]
      congr 1
      field_simp [hc j]
    rw [←Matrix.mulVec_smul] at hh
    exact point_projectively_injective f i j _ (hi hh)
  let e : Equiv.Perm (Fin 24) := Equiv.ofBijective σ
    ⟨hs,Finite.surjective_of_injective hs⟩
  exact ⟨e,c,hc,he⟩

/-- Fixed finite family installation; complex equality and scalar choices
are classical. This is not a claimed byte-level root-recognition machine. -/
def rootAction (f : Form) (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots f) A) : RootAction f A := by
  let ex := rootAction_exists f A hd h
  let σ := Classical.choose ex
  let c := Classical.choose (Classical.choose_spec ex)
  have hc := Classical.choose_spec (Classical.choose_spec ex)
  exact ⟨σ,c,hc.1,hc.2⟩

theorem RootAction.perm_unique {f : Form} {A : End}
    (p q : RootAction f A) : p.perm = q.perm := by
  apply Equiv.ext
  intro i
  have hh : point f (p.perm i) =
      ((p.scale i)⁻¹ * q.scale i) • point f (q.perm i) := by
    calc
      point f (p.perm i) = (p.scale i)⁻¹ • (A *ᵥ point f i) := by
        rw [p.image_eq,smul_smul,inv_mul_cancel₀ (p.scale_ne_zero i),one_smul]
      _ = _ := by rw [q.image_eq,smul_smul]
  exact point_projectively_injective f _ _ _ hh

theorem RootAction.scale_unique {f : Form} {A : End}
    (p q : RootAction f A) : p.scale = q.scale := by
  funext i
  have hh := (p.image_eq i).symm.trans (q.image_eq i)
  rw [p.perm_unique q] at hh
  obtain ⟨j,hj⟩ := Function.ne_iff.mp (point_ne_zero f (q.perm i))
  apply mul_right_cancel₀ hj
  simpa only [Pi.smul_apply,smul_eq_mul] using congrFun hh j

theorem RootAction.inverse_image {f : Form} {A : End}
    (p : RootAction f A) (hd : A.det ≠ 0) (i : Fin 24) :
    A⁻¹ *ᵥ point f i = (p.scale (p.perm.symm i))⁻¹ • point f (p.perm.symm i) := by
  have hh := congrArg (fun v : V => A⁻¹ *ᵥ v) (p.image_eq (p.perm.symm i))
  simp only [p.perm.apply_symm_apply,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec,
    Matrix.mulVec_smul] at hh
  calc
    A⁻¹ *ᵥ point f i = (p.scale (p.perm.symm i))⁻¹ •
        (p.scale (p.perm.symm i) • (A⁻¹ *ᵥ point f i)) := by
      rw [smul_smul,inv_mul_cancel₀ (p.scale_ne_zero _),one_smul]
    _ = _ := by rw [←hh]

def RootAction.inverse {f : Form} {A : End}
    (p : RootAction f A) (hd : A.det ≠ 0) : RootAction f A⁻¹ where
  perm := p.perm.symm
  scale i := (p.scale (p.perm.symm i))⁻¹
  scale_ne_zero i := inv_ne_zero (p.scale_ne_zero _)
  image_eq := p.inverse_image hd

theorem inverse_oneSided (f : Form) (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots f) A) : OneSided (Roots f) A⁻¹ := by
  let p := rootAction f A hd h
  intro v hv
  obtain ⟨i,c,hc,rfl⟩ := (roots_iff f v).mp hv
  rw [Matrix.mulVec_smul,p.inverse_image hd,smul_smul]
  exact Or.inr ((roots_iff f _).mpr
    ⟨p.perm.symm i,c*(p.scale (p.perm.symm i))⁻¹,
      mul_ne_zero hc (inv_ne_zero (p.scale_ne_zero _)),rfl⟩)

/-- The image equation is about the old ordered contraction with the
literal output X. It does not silently identify transfer and card maps. -/
theorem ordered_card_image (f : Form) (q : FourTensor) (e : PortOrder)
    (p : RootAction f (transferMatrix q e)) (k : Fin 24) :
    coordinates (rawCard q e (kernel f k)*Holant.Certificates.MatchingContractionClosure.X) =
      p.scale k • point f (p.perm k) := by
  rw [←transfer_action q e (kernel f k)]
  exact p.image_eq k

theorem ordered_card_ne_zero (f : Form) (q : FourTensor) (e : PortOrder)
    (p : RootAction f (transferMatrix q e)) (k : Fin 24) :
    rawCard q e (kernel f k) ≠ 0 := by
  intro hz
  have hh := ordered_card_image f q e p k
  rw [hz,Matrix.zero_mul,map_zero] at hh
  exact (smul_ne_zero (p.scale_ne_zero k) (point_ne_zero f (p.perm k))) hh.symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
