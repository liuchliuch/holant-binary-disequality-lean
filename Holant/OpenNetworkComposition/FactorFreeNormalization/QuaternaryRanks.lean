import Holant.OpenNetworkComposition.FactorFreeNormalization.PairRanks
import Holant.Certificates.MatchingProductBridge.Flattenings

/-! The three usual quaternary flattenings already exclude every isolated
native-X pair factor, independently of the order of its two selected ports. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Holant.OpenNetworkComposition.FactorFreeNormalization
open Holant.Certificates.MatchingProductBridge

private def word (r : Fin 3) (a b : Bool × Bool) : Fin 4 → Bool :=
  if r=0 then ![a.1,a.2,b.1,b.2] else if r=1 then ![a.1,b.1,a.2,b.2]
  else ![a.1,b.1,b.2,a.2]

private theorem flatten_word (r : Fin 3) (h : Signature ℂ 4) (a b : Bool × Bool) :
    flatten r h a b=h (word r a b) := by
  fin_cases r <;> rfl

private theorem row_factor_rank (h : Signature ℂ 4) (i j : Fin 4)
    (g : Tensor ℂ (OtherPorts i j))
    (hg : ∀x,h x=Signature.disequality (x i) (x j)*g (fun k => x k.val))
    (r : Fin 3)
    (hi : ∀a b,word r a b i=word r a (false,false) i)
    (hj : ∀a b,word r a b j=word r a (false,false) j)
    (hk : ∀a b (k : OtherPorts i j),word r a b k.val=word r (false,false) b k.val) :
    (flatten r h).rank≤1 := by
  let u := fun a => Signature.disequality (K := ℂ)
    (word r a (false,false) i) (word r a (false,false) j)
  let v := fun b => g (fun k => word r (false,false) b k.val)
  have he : flatten r h=Matrix.vecMulVec u v := by
    ext a b
    rw [flatten_word,hg,hi,hj]
    change _*g (fun k => word r a b k.val)=_*g (fun k => word r (false,false) b k.val)
    congr 1
    congr 1
    funext k
    exact hk a b k
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

private theorem col_factor_rank (h : Signature ℂ 4) (i j : Fin 4)
    (g : Tensor ℂ (OtherPorts i j))
    (hg : ∀x,h x=Signature.disequality (x i) (x j)*g (fun k => x k.val))
    (r : Fin 3)
    (hi : ∀a b,word r a b i=word r (false,false) b i)
    (hj : ∀a b,word r a b j=word r (false,false) b j)
    (hk : ∀a b (k : OtherPorts i j),word r a b k.val=word r a (false,false) k.val) :
    (flatten r h).rank≤1 := by
  let u := fun a => g (fun k => word r a (false,false) k.val)
  let v := fun b => Signature.disequality (K := ℂ)
    (word r (false,false) b i) (word r (false,false) b j)
  have he : flatten r h=Matrix.vecMulVec u v := by
    ext a b
    rw [flatten_word,hg,hi,hj]
    change _*g (fun k => word r a b k.val)=g (fun k => word r a (false,false) k.val)*_
    rw [mul_comm]
    congr 1
    congr 1
    funext k
    exact hk a b k
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

/-- Whichever distinct two original coordinates carry X, its matching
flattening is an actual rank-at-most-one outer product. -/
theorem hasXFactor_rank_le_one {h : Signature ℂ 4} (hf : HasXFactor h) :
    ∃r : Fin 3,(flatten r h).rank≤1 := by
  obtain ⟨i,j,hij,g,hg⟩ := hf
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals first
    | (refine ⟨0,row_factor_rank h _ _ g hg 0 ?_ ?_ ?_⟩
       · intro a b; rfl
       · intro a b; rfl
       · intro a b k; rcases k with ⟨k,hk⟩; fin_cases k <;> first | exact (hk.1 rfl).elim | exact (hk.2 rfl).elim | rfl)
    | (refine ⟨1,row_factor_rank h _ _ g hg 1 ?_ ?_ ?_⟩
       · intro a b; rfl
       · intro a b; rfl
       · intro a b k; rcases k with ⟨k,hk⟩; fin_cases k <;> first | exact (hk.1 rfl).elim | exact (hk.2 rfl).elim | rfl)
    | (refine ⟨2,row_factor_rank h _ _ g hg 2 ?_ ?_ ?_⟩
       · intro a b; rfl
       · intro a b; rfl
       · intro a b k; rcases k with ⟨k,hk⟩; fin_cases k <;> first | exact (hk.1 rfl).elim | exact (hk.2 rfl).elim | rfl)
    | (refine ⟨0,col_factor_rank h _ _ g hg 0 ?_ ?_ ?_⟩
       · intro a b; rfl
       · intro a b; rfl
       · intro a b k; rcases k with ⟨k,hk⟩; fin_cases k <;> first | exact (hk.1 rfl).elim | exact (hk.2 rfl).elim | rfl)
    | (refine ⟨1,col_factor_rank h _ _ g hg 1 ?_ ?_ ?_⟩
       · intro a b; rfl
       · intro a b; rfl
       · intro a b k; rcases k with ⟨k,hk⟩; fin_cases k <;> first | exact (hk.1 rfl).elim | exact (hk.2 rfl).elim | rfl)
    | (refine ⟨2,col_factor_rank h _ _ g hg 2 ?_ ?_ ?_⟩
       · intro a b; rfl
       · intro a b; rfl
       · intro a b k; rcases k with ⟨k,hk⟩; fin_cases k <;> first | exact (hk.1 rfl).elim | exact (hk.2 rfl).elim | rfl)

/-- Rank at least two in the three conventional flattenings suffices;
in particular this applies to every rank-(3,3,3) quaternary. -/
theorem noXFactor_of_threeRanks (h : Signature ℂ 4)
    (hr : ∀r : Fin 3,2≤(flatten r h).rank) : NoXFactor h := by
  intro hf
  obtain ⟨r,hu⟩ := hasXFactor_rank_le_one hf
  have hl := hr r
  omega

end Holant.OpenNetworkComposition.FactorFreeNormalization
