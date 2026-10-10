import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSystematicSupport
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionCoordinates

/-! Coordinate-cube reconstruction for literal Affine functions. Third ratios
are tested only on three coordinate directions, including repetitions, at
all actual base words. This supplies the low-rank pinned-face criterion used
on internally selected systematic support coordinates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineThreeFaces
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n : ℕ}

def CoordinateCubes (f : Signature AlgebraicComplex n) : Prop :=
  ∀z : Word n,∀i j k : Fin n,thirdRatio f z (basis i) (basis j) (basis k)=1

theorem secondRatio_step (f : Signature AlgebraicComplex n) (full : ∀x,f x≠0)
    (z u v w : Word n) (h : thirdRatio f z u v w=1) :
    secondRatio f (xor z w) u v=secondRatio f z u v := by
  have hh := (thirdRatio_eq_one_iff full z u v w).mp h
  have swap (a b c : Word n) : xor (xor a b) c=xor (xor a c) b := by
    rw [xor_assoc,xor_comm b c,←xor_assoc]
  simp only [secondRatio]
  rw [swap z w u,swap (xor z u) w v,swap z w v]
  apply (div_eq_div_iff (mul_ne_zero (full _) (full _)) (mul_ne_zero (full _) (full _))).mpr
  linear_combination hh

/-- Coordinate edges connect the entire Boolean cube, so testing every
coordinate third ratio makes each coordinate-pair second ratio constant. -/
theorem secondRatio_constant_coordinates (f : Signature AlgebraicComplex n)
    (full : ∀x,f x≠0) (cubes : CoordinateCubes f) (z : Word n) (i j : Fin n) :
    secondRatio f z (basis i) (basis j)=secondRatio f (origin n) (basis i) (basis j) := by
  apply GeneralEOPairedFamilyExtractionFullSupport.constant_of_coordinates n
    (fun z=>secondRatio f z (basis i) (basis j)) _ z (origin n)
  intro k x
  have he : xor (Function.update x k false) (basis k)=Function.update x k true := by
    funext l
    by_cases hl : l=k
    · subst l
      simp [AffinePhase.xor,basis]
    · simp [AffinePhase.xor,basis,hl]
  have h := secondRatio_step f full (Function.update x k false) (basis i) (basis j) (basis k)
    (cubes _ i j k)
  rw [he] at h
  exact h.symm

variable (f : Signature AlgebraicComplex n) (full : ∀x,f x≠0) (cubes : CoordinateCubes f)

include full cubes in
theorem linear_four (j : Fin n) : linearCoefficient f j^4=1 := by
  have hh := (thirdRatio_eq_one_iff full (origin n) (basis j) (basis j) (basis j)).mp
    (cubes _ j j j)
  simp only [origin_xor,AffinePhase.xor_self] at hh
  have equal : f (basis j)^4=f (origin n)^4 := by linear_combination hh
  rw [linearCoefficient,div_pow,equal,div_self (pow_ne_zero _ (full _))]

include full cubes in
theorem mixed_square (i j : Fin n) : mixedCoefficient f i j^2=1 := by
  have hh := secondRatio_constant_coordinates f full cubes (basis i) i j
  simp only [secondRatio,origin_xor,AffinePhase.xor_self] at hh
  have hc := (div_eq_div_iff (mul_ne_zero (full _) (full _)) (mul_ne_zero (full _) (full _))).mp hh
  simp only [mixedCoefficient,secondRatio,origin_xor,div_pow]
  apply (div_eq_one_iff_eq (pow_ne_zero 2 (mul_ne_zero (full _) (full _)))).mpr
  linear_combination -hc

include full cubes in
theorem firstRatio_translate_coordinates (z : Word n) (i j : Fin n) :
    f (xor (xor z (basis j)) (basis i))/f (xor z (basis j))=
      mixedCoefficient f i j*(f (xor z (basis i))/f z) := by
  have hh := secondRatio_constant_coordinates f full cubes z i j
  have hc := (div_eq_iff (mul_ne_zero (full _) (full _))).mp hh
  have swap : xor (xor z (basis j)) (basis i)=xor (xor z (basis i)) (basis j) := by
    rw [xor_assoc,xor_comm (basis j) (basis i),←xor_assoc]
  rw [swap]
  dsimp only [mixedCoefficient]
  field_simp [full]
  linear_combination hc

include full cubes in
theorem firstRatio_word_coordinates (j : Fin n) (s : Finset (Fin n)) :
    f (xor (word s) (basis j))/f (word s)=
      linearCoefficient f j*∏k∈s,mixedCoefficient f j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linearCoefficient]
  | @insert k s hk ih =>
    rw [word_insert s k hk,firstRatio_translate_coordinates f full cubes,ih,Finset.prod_insert hk]
    ring

include full cubes in
theorem value_insert_coordinates (j : Fin n) (s : Finset (Fin n)) (hj : j∉s) :
    f (word (insert j s))=f (word s)*linearCoefficient f j*∏k∈s,mixedCoefficient f j k := by
  rw [word_insert s j hj]
  have h := (div_eq_iff (full (word s))).mp (firstRatio_word_coordinates f full cubes j s)
  linear_combination h

include full cubes in
/-- The coordinate-cube test reconstructs an explicit finite-system,
even-quadratic Affine witness at every arity. -/
theorem affine_of_coordinate_cubes : Affine f := by
  classical
  have ha : ∀j : Fin n,∃q : ZMod 4,fourthRootPhase q=linearCoefficient f j :=
    fun j=>fourthRootPhase_surjective_of_pow_four (linear_four f full cubes j)
  choose a ha using ha
  have hb : ∀j k : Fin n,∃q : ZMod 4,(q=0 ∨ q=2) ∧ fourthRootPhase q=mixedCoefficient f j k :=
    fun j k=>evenPhase_of_sq_eq_one (mixed_square f full cubes j k)
  choose b hb hphase using hb
  let Q : QuadraticPhase n := ⟨0,a,b,fun j k _=>hb j k⟩
  have hv (s : Finset (Fin n)) : f (word s)=f (origin n)*fourthRootPhase (Q.eval (word s)) := by
    induction s using Finset.induction_on_max with
    | empty => rw [quadratic_eval_word];simp [Q]
    | insert j s hmax ih =>
      have hj : j∉s := fun h=>(lt_irrefl j) (hmax j h)
      rw [value_insert_coordinates f full cubes j s hj,ih,
        quadratic_eval_insert_max Q s j hj hmax,fourthRootPhase_add,fourthRootPhase_add,
        fourthRootPhase_sum]
      change _=f (origin n)*(fourthRootPhase (Q.eval (word s))*fourthRootPhase (a j)*
        ∏k∈s,fourthRootPhase (b k j))
      simp_rw [ha,hphase,mixedCoefficient_comm f _ j]
      ring
  right
  refine ⟨f (origin n),full _,AffineSystem.unconstrained n,Q,?_⟩
  funext x
  let s : Finset (Fin n) := Finset.univ.filter (fun j=>x j=true)
  have hs : word s=x := by funext j;simp [word,s]
  simpa [affineFormula,hs] using hv s


/-- All coordinates outside S are literally fixed to the displayed word. -/
def face (f : Signature AlgebraicComplex n) (S : Finset (Fin n)) (z : Word n) : Signature AlgebraicComplex n :=
  fun x=>if ∀i,i∉S → x i=z i then f x else 0

theorem coordinate_cube_face (f : Signature AlgebraicComplex n) (z : Word n)
    (i j k : Fin n) (v : Fin 8) :
    face f {i,j,k} z (Holant.ReedMuller.AffinePatching.cubeWords z (basis i) (basis j) (basis k) v)=
      f (Holant.ReedMuller.AffinePatching.cubeWords z (basis i) (basis j) (basis k) v) := by
  apply ite_eq_left
  intro a ha
  have h : a≠i ∧ a≠j ∧ a≠k := by simpa using ha
  fin_cases v <;> simp [Holant.ReedMuller.AffinePatching.cubeWords,AffinePhase.xor,basis,h.1,h.2.1,h.2.2]

include full in
theorem cube_of_affine_face (z : Word n) (i j k : Fin n)
    (ha : Affine (face f {i,j,k} z)) : thirdRatio f z (basis i) (basis j) (basis k)=1 := by
  have h := Holant.ReedMuller.AffinePatching.affine_supported_cube
    (face f {i,j,k} z) ha z (basis i) (basis j) (basis k)
    (fun v=>by rw [coordinate_cube_face];exact full _)
  let w := Holant.ReedMuller.AffinePatching.cubeWords z (basis i) (basis j) (basis k)
  change (face f {i,j,k} z (w 7)*face f {i,j,k} z (w 1)*face f {i,j,k} z (w 2)*face f {i,j,k} z (w 3))/
    (face f {i,j,k} z (w 4)*face f {i,j,k} z (w 5)*face f {i,j,k} z (w 6)*face f {i,j,k} z (w 0))=1 at h
  simp only [w,coordinate_cube_face] at h
  exact h

include full in
/-- Every assignment of the pinned coordinates is tested, not just origin
faces. Repeated coordinate directions are included in the reconstruction. -/
theorem affine_of_three_faces
    (faces : ∀S : Finset (Fin n),S.card≤3 → ∀z : Word n,Affine (face f S z)) : Affine f := by
  apply affine_of_coordinate_cubes f full
  intro z i j k
  exact cube_of_affine_face f full z i j k (faces {i,j,k} (by
    have h := Finset.card_insert_le i ({j,k} : Finset (Fin n))
    have hh := Finset.card_insert_le j ({k} : Finset (Fin n))
    simp only [Finset.card_singleton] at hh
    omega) z)

include full in
/-- A full-support failure supplies an actual nonaffine pinned face with at
most three free coordinates, with its real outside assignment retained. -/
theorem exists_bad_face (bad : ¬Affine f) :
    ∃S : Finset (Fin n),S.card≤3 ∧ ∃z : Word n,¬Affine (face f S z) := by
  classical
  by_contra absent
  push Not at absent
  exact bad (affine_of_three_faces f full absent)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeAffineThreeFaces
end
