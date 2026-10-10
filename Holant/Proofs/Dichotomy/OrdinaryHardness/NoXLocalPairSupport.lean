import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSystematicSupport

/-! A literal relation between two independent information ports lowers
support rank by one. The opposite graph retains two equal exposed copies,
flips its first input port, and keeps both nonzero antidiagonal weights. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalPairSupport
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n r : ℕ}

def flipAt (p : Fin n) (x : Word n) : Word n := Function.update x p (!(x p))

@[simp] theorem flip_at (p : Fin n) (x : Word n) : flipAt p x p=!(x p) := by simp [flipAt]
theorem flip_ne (p q : Fin n) (h : q≠p) (x : Word n) : flipAt p x q=x q := by simp [flipAt,h]
@[simp] theorem flip_involutive (p : Fin n) (x : Word n) : flipAt p (flipAt p x)=x := by
  funext i
  by_cases hi : i=p
  · subst i;simp
  · rw [flip_ne p i hi,flip_ne p i hi]

theorem flip_affine (p : Fin n) : TwoTranslate.IsAffineMap (flipAt p) := by
  intro x y
  funext i
  by_cases hi : i=p
  · subst i
    cases hx : x p <;> cases hy : y p <;> simp [flipAt,AffinePhase.xor,AffinePhase.origin,hx,hy]
  · simp [flipAt,AffinePhase.xor,AffinePhase.origin,hi]

def equalMask (f : Signature AlgebraicComplex n) (p q : Fin n) : Signature AlgebraicComplex n :=
  fun x=>if x p=x q then f x else 0

def oppositeMerge (f : Signature AlgebraicComplex n) (p q : Fin n) (v w : AlgebraicComplex) :
    Signature AlgebraicComplex n := fun x=>if x p=x q then (if x p then v else w)*f (flipAt p x) else 0

def duplicate (z : Word (r+1)) : Word (r+2) := Fin.cons (z 0) z

def opposite (z : Word (r+1)) : Word (r+2) := Fin.cons (!(z 0)) z

theorem duplicate_affine : TwoTranslate.IsAffineMap (duplicate (r:=r)) := by
  have he : duplicate (r:=r)=(fun z i=>z ((Fin.cases (0 : Fin (r+1)) id : Fin (r+2)→Fin (r+1)) i)) := by
    funext z i
    refine Fin.cases ?_ (fun j=>?_) i <;> rfl
  rw [he]
  exact coordinates_isAffineMap _

theorem opposite_affine : TwoTranslate.IsAffineMap (opposite (r:=r)) := by
  intro x y
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · cases hx : x 0 <;> cases hy : y 0 <;> simp [opposite,AffinePhase.xor,AffinePhase.origin,hx,hy]
  · simp [opposite,AffinePhase.xor,AffinePhase.origin]

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f (r+2))

theorem port_ne (j : Fin (r+1)) : D.ports j.succ≠D.ports 0 := by
  intro he
  exact Fin.succ_ne_zero j (D.injective he)

def equalChart : SystematicSupport (equalMask f (D.ports 0) (D.ports (Fin.succ 0))) (r+1) where
  ports j := D.ports j.succ
  injective := D.injective.comp (Fin.succ_injective _)
  encode z := D.encode (duplicate z)
  affine := affine_map_comp D.encode duplicate D.affine duplicate_affine
  free z i := by rw [D.free];rfl
  supported z := by
    have he : D.encode (duplicate z) (D.ports 0)=D.encode (duplicate z) (D.ports (Fin.succ 0)) := by
      rw [D.free,D.free]
      rfl
    rw [equalMask,ite_eq_left he]
    exact D.supported _
  covers x hx := by
    have he : x (D.ports 0)=x (D.ports (Fin.succ 0)) := by
      by_contra hn
      exact hx (by rw [equalMask,ite_eq_right hn])
    have hf : f x≠0 := by simpa only [equalMask,ite_eq_left he] using hx
    have word : duplicate (fun j=>x (D.ports j.succ))=(fun j=>x (D.ports j)) := by
      funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · exact he.symm
      · rfl
    rw [word]
    exact D.covers x hf

variable (v w : AlgebraicComplex) (hv : v≠0) (hw : w≠0)

def oppositeChart : SystematicSupport (oppositeMerge f (D.ports 0) (D.ports (Fin.succ 0)) v w) (r+1) where
  ports j := D.ports j.succ
  injective := D.injective.comp (Fin.succ_injective _)
  encode z := flipAt (D.ports 0) (D.encode (opposite z))
  affine := affine_map_comp (flipAt (D.ports 0)) (fun z=>D.encode (opposite z)) (flip_affine _)
    (affine_map_comp D.encode opposite D.affine opposite_affine)
  free z i := by
    rw [flip_ne _ _ (port_ne D i),D.free]
    rfl
  supported z := by
    have he : flipAt (D.ports 0) (D.encode (opposite z)) (D.ports 0)=
        flipAt (D.ports 0) (D.encode (opposite z)) (D.ports (Fin.succ 0)) := by
      rw [flip_at,flip_ne _ _ (port_ne D 0),D.free,D.free]
      simp [opposite]
    rw [oppositeMerge,ite_eq_left he,flip_involutive]
    apply mul_ne_zero ?_ (D.supported _)
    split_ifs
    · exact hv
    · exact hw
  covers x hx := by
    have he : x (D.ports 0)=x (D.ports (Fin.succ 0)) := by
      by_contra hn
      exact hx (by rw [oppositeMerge,ite_eq_right hn])
    have hf : f (flipAt (D.ports 0) x)≠0 := by
      intro zero
      exact hx (by simp [oppositeMerge,zero])
    have word : opposite (fun j=>x (D.ports j.succ))=(fun j=>flipAt (D.ports 0) x (D.ports j)) := by
      funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · change (!(x (D.ports (Fin.succ 0))))=flipAt (D.ports 0) x (D.ports 0)
        rw [flip_at,he]
      · exact (flip_ne _ _ (port_ne D j) x).symm
    rw [word,D.covers _ hf,flip_involutive]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalPairSupport
end
