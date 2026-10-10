import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenAntiSigned
import Holant.Proofs.Hardness.GeneralEOBinarySignedHardness

/-! All four signed binary rows are actual even blocks with one common
private-variable bound. Their complete coefficients retain the anti guard's
uniform scalar, ready for the counted-verifier signed-binary source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiFamily
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace S
export NoXGeneralEvenAntiSigned (block block_value)
end S
namespace Q
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeQuery (count signs)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignedHardness (pairings)
end Q
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
namespace C
export OrdinaryNegativeMixedBlockPrivateComposeCore (freshCount Private node Occurrence)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {b : ℕ→ℕ}

abbrev count := Q.count (arity:=fun _=>4) Q.pairings
abbrev signs (i : Fin count) : Fin 2→Bool := Q.signs (arity:=fun _=>4) Q.pairings i

variable (row antiRow : B.Block (s:=s) (b:=b) 2)

def privateCount : ℕ := (S.block row antiRow (fun _=>false)).privateCount

private theorem fresh_count {u d l : ℕ} {a : ℕ→ℕ}
    (outer : Recipe (u:=1) (s:=u) (a:=fun _=>d+l) (b:=a)) (k : Fin u→ℕ) :
    C.freshCount outer k=((outer 0).map (fun node=>k node.1)).sum := by
  unfold C.freshCount C.Private
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [←List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map (outer 0) (fun node=>k node.1))

theorem privateCount_eq (sign : Fin 2→Bool) :
    (S.block row antiRow sign).privateCount=privateCount row antiRow := by
  change 2+C.freshCount (NoXGeneralEvenAntiSigned.outer sign)
      (NoXGeneralEvenCompose.counts (NoXGeneralEvenAntiSigned.resources row antiRow))=
    2+C.freshCount (NoXGeneralEvenAntiSigned.outer (fun _=>false))
      (NoXGeneralEvenCompose.counts (NoXGeneralEvenAntiSigned.resources row antiRow))
  rw [fresh_count,fresh_count]
  congr 2


def castRows {n k : ℕ} (D : B.Block (s:=s) (b:=b) n) (h : D.privateCount=k) :
    Recipe (u:=1) (s:=s) (a:=fun _=>n+k) (b:=b) := h ▸ D.rows

theorem cast_balanced {n k : ℕ} (D : B.Block (s:=s) (b:=b) n) (h : D.privateCount=k) :
    EvenRecipe (castRows D h) := by
  subst k
  exact D.balanced

def rows : Recipe (u:=count) (s:=s) (a:=fun _=>2+privateCount row antiRow) (b:=b) :=
  fun i=>castRows (S.block row antiRow (signs i)) (privateCount_eq row antiRow (signs i)) 0

theorem balanced : EvenRecipe (rows row antiRow) := by
  intro i p
  exact cast_balanced (S.block row antiRow (signs i)) (privateCount_eq row antiRow (signs i)) 0 p

variable {K : Type} [Field K] [Algebra ℚ K] (H : (j : Fin s)→Signature K (b j.val))
variable (v w : K) (anti : antiRow.signature H=NoXWeightedAntiSigned.anti v w)

omit [Algebra ℚ K] in
theorem cast_value {n k : ℕ} (D : B.Block (s:=s) (b:=b) n) (h : D.privateCount=k) (z : Fin n→Bool) :
    M.trace H k (castRows D h) 0 z=D.signature H z := by
  subst k
  rfl

include anti in
theorem value (i : Fin count) (z : Fin 2→Bool) :
    M.trace H (privateCount row antiRow) (rows row antiRow) i z=
      (v*w)^2*row.signature H (fun j=>Bool.xor (signs i j) (z j)) := by
  change M.trace H (privateCount row antiRow)
    (castRows (S.block row antiRow (signs i)) (privateCount_eq row antiRow (signs i))) 0 z=_
  rw [cast_value,S.block_value row antiRow (signs i) H v w anti]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiFamily
end
