import Holant.Certificates.RainbowOrbit.FamilyGeometry
import Holant.Certificates.RainbowOrbit.PhysicalSingleLeg

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem points_map (p : Fin 3→Point) (f : Point→Point) (hf : Function.Injective f) :
    points (fun r => f (p r))=(points p).map ⟨f,hf⟩ := by
  classical
  ext x
  simp [points]

theorem points_permute (p : Fin 3→Point) (e : Equiv.Perm (Fin 3)) :
    points (fun r => p (e r))=points p := by
  classical
  apply Finset.coe_injective
  have hcoe (q : Fin 3→Point) : (points q : Set Point)=Set.range q := by ext x; simp [points]
  rw [hcoe,hcoe,range_permute]

inductive Operation (n : ℕ) where
  | dress (port : Fin 4) (index : Fin n)
  | swap (port : Fin 3)
  deriving DecidableEq,Fintype

theorem singleLeg_det (M : BinaryMatrix) (hM : M.det≠0) (j : Fin 4) :
    ∀q,(physicalSingleLeg j M q).det≠0 := by
  intro q
  by_cases h : q=j
  · simp [physicalSingleLeg,h,hM]
  · simp [physicalSingleLeg,h]

def operationPoint {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,(R i).det≠0) : Operation n→(Point↪Point)
  | .dress j i => ⟨pointAction (physicalSingleLeg j (R i)) (singleLeg_det _ (hR i) j),pointAction_injective _ _⟩
  | .swap j => ⟨portPoint (adjacent j),portPoint_injective _⟩

def runPointWord {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,(R i).det≠0) : List (Operation n)→Point→Point
  | [],p => p
  | o::w,p => runPointWord R hR w (operationPoint R hR o p)

theorem runPointWord_injective {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,(R i).det≠0)
    (w : List (Operation n)) : Function.Injective (runPointWord R hR w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons o w ih => exact ih.comp (operationPoint R hR o).injective

def runWord {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,(R i).det≠0)
    (w : List (Operation n)) (S : Finset Point) : Finset Point :=
  S.map ⟨runPointWord R hR w,runPointWord_injective R hR w⟩

def fourWord {n : ℕ} (k : Fin 4→Fin n) : List (Operation n) :=
  [.dress 0 (k 0),.dress 1 (k 1),.dress 2 (k 2),.dress 3 (k 3)]

theorem fourWord_action {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,(R i).det≠0)
    (k : Fin 4→Fin n) (p : Point) :
    runPointWord R hR (fourWord k) p=pointAction (fun j => R (k j)) (fun j => hR (k j)) p := by
  induction p using Projectivization.ind with | h F hF =>
  simp only [fourWord,runPointWord,operationPoint,Function.Embedding.coeFn_mk,pointAction_mk]
  congr 1
  exact act_four_leg_word F (fun j => R (k j))

theorem runWord_four {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,(R i).det≠0)
    (k : Fin 4→Fin n) (S : Finset Point) :
    runWord R hR (fourWord k) S=S.map
      ⟨pointAction (fun j => R (k j)) (fun j => hR (k j)),pointAction_injective _ _⟩ := by
  unfold runWord
  congr 1
  apply Function.Embedding.ext
  exact fourWord_action R hR k

theorem FamilyRainbowLine.operation {G : BinaryMatrix→Prop} (hG : MatrixFamily G)
    {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,G (R i))
    (o : Operation n) {S : Finset Point} (hS : FamilyRainbowLine G S) :
    FamilyRainbowLine G (S.map (operationPoint R (fun i => hG.nonsingular (hR i)) o)) := by
  obtain ⟨p,hp,rfl⟩ := hS
  cases o with
  | dress j i =>
    have hm : ∀q,G (physicalSingleLeg j (R i) q) := by
      intro q
      by_cases h : q=j
      · simpa [physicalSingleLeg,h] using hR i
      · simpa [physicalSingleLeg,h] using hG.one
    refine ⟨_,FamilyRainbow.map_act (G := G) (fun {U} h => hG.transpose h)
      (fun {U V} h h' => hG.mul h h') hp _ hm (singleLeg_det _ (hG.nonsingular (hR i)) j),?_⟩
    exact (points_map p _ (pointAction_injective _ _)).symm
  | swap j =>
    refine ⟨_,FamilyRainbow.map_adjacent (G := G) (fun {U} h => hG.transpose h) hp j,?_⟩
    rw [←points_map]
    exact (points_permute (fun r => portPoint (adjacent j) (p r)) (adjacentLabels j).symm).symm

theorem FamilyRainbowLine.word {G : BinaryMatrix→Prop} (hG : MatrixFamily G)
    {n : ℕ} (R : Fin n→BinaryMatrix) (hR : ∀i,G (R i))
    (w : List (Operation n)) {S : Finset Point} (hS : FamilyRainbowLine G S) :
    FamilyRainbowLine G (runWord R (fun i => hG.nonsingular (hR i)) w S) := by
  induction w generalizing S with
  | nil =>
    have he : runWord R (fun i => hG.nonsingular (hR i)) [] S=S := by
      ext p
      simp [runWord,runPointWord]
    rwa [he]
  | cons o w ih =>
    have hh := ih (hS.operation hG R hR o)
    have he : runWord R (fun i => hG.nonsingular (hR i)) (o::w) S=
        runWord R (fun i => hG.nonsingular (hR i)) w
          (S.map (operationPoint R (fun i => hG.nonsingular (hR i)) o)) := by
      simp only [runWord,Finset.map_map]
      rfl
    rw [he]
    exact hh

end
end Holant.Certificates.RainbowOrbit
