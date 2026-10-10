import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockData
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticParityFourierTyped

/-! Fixed mixed-label recipe for the cubic/Eq4/two-pin source palette.
Every row gets51 private ports. The cubic row uses the literal Fourier block;
all other rows are doubled and each private port is fixed by two actual pin0
rows. All scopes are variable scopes, including the shared Fourier constant. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticFourierRecipe
open Holant Holant.Tractable
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace D
export OrdinaryNegativeMixedBlockData (Recipe Node ports EvenRecipe coefficient)
end D
namespace P
export OrdinaryNegativePhaseBundleRaw (sourceArity sourceRows)
end P
namespace F
export OrdinaryNegativeOcticParityFourier (factors)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option Elab.async false

def targetArity : ℕ → ℕ
  | 0 => 2
  | 4 => 4
  | _ => 1

def expanded (i : ℕ) : ℕ := P.sourceArity i+51

def oldLabel (i : Fin 4) : ℕ := if i.val=1 then 4 else if i.val=2 then 2 else 3

def otherRows (i : Fin 4) : List Factor :=
  [(oldLabel i,List.range (P.sourceArity i.val)),(oldLabel i,List.range (P.sourceArity i.val))] ++
  (List.range 51).flatMap (fun j=>[(2,[P.sourceArity i.val+j]),(2,[P.sourceArity i.val+j])])

def rows (i : Fin 4) : List Factor := if i.val=0 then F.factors else otherRows i

theorem rows_valid : ∀i : Fin 4,∀r∈rows i,
    r.1<5 ∧ r.2.length=targetArity r.1 ∧ ∀j∈r.2,j<expanded i.val := by decide

def node (i : Fin 4) (r : Factor) (hr : r∈rows i) :
    D.Node (u:=4) (s:=5) (a:=expanded) (b:=targetArity) i :=
  ⟨⟨r.1,(rows_valid i r hr).1⟩,fun j=>.inr
    ⟨r.2.get ⟨j.val,by exact Nat.lt_of_lt_of_eq j.isLt (rows_valid i r hr).2.1.symm⟩,
      (rows_valid i r hr).2.2 _ (List.get_mem _ _)⟩⟩

def recipe : D.Recipe (u:=4) (s:=5) (a:=expanded) (b:=targetArity) :=
  fun i=>(rows i).attach.map (fun r=>node i r.val r.property)

theorem even_recipe : D.EvenRecipe recipe := by
  unfold OrdinaryNegativeMixedBlockData.EvenRecipe
  decide

variable {K : Type} [CommRing K]
def table (z : K) (i : Fin 5) : Signature K (targetArity i.val) :=
  match i with
  | ⟨0,_⟩ => fun (x : Fin 2 → Bool)=>OrdinaryNegativeOcticParityFourier.character (x 0) (x 1)
  | ⟨1,_⟩ => fun (x : Fin 1 → Bool)=>z^(x 0).toNat
  | ⟨2,_⟩ => Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false
  | ⟨3,_⟩ => Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true
  | ⟨4,_⟩ => Holant.EightVertex.ProductAnchor.equalityFour
  | ⟨k+5,h⟩ => False.elim (by omega)

def trace (z : K) (i : Fin 4) (x : Fin (P.sourceArity i.val) → Bool) : K :=
  ∑y : Fin 51 → Bool,D.coefficient (table z) recipe i (Fin.addCases x y)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticFourierRecipe
end
