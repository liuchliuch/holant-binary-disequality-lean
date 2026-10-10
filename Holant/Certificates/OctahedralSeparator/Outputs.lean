import Holant.Certificates.OctahedralSeparator.EndpointInteger
import Holant.Certificates.OctahedralSeparator.PreparedCache

namespace Holant.Certificates.OctahedralSeparator
open Holant
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem endpoint_exact (j : Fin 48) (h : ¬outsideRow j) :
    endpointOutput j=Signature.coordinateAction (endpointLegs j) (prepared j) :=
  endpoint_integer_certificate j h

theorem outside_exact_21 : (fun x : Fin 2 → Bool => outsideValues 21 (x 0) (x 1)) = Signature.contract (closureKernel 21) (prepared 21) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_22 : (fun x : Fin 2 → Bool => outsideValues 22 (x 0) (x 1)) = Signature.contract (closureKernel 22) (prepared 22) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_23 : (fun x : Fin 2 → Bool => outsideValues 23 (x 0) (x 1)) = Signature.contract (closureKernel 23) (prepared 23) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_24 : (fun x : Fin 2 → Bool => outsideValues 24 (x 0) (x 1)) = Signature.contract (closureKernel 24) (prepared 24) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_25 : (fun x : Fin 2 → Bool => outsideValues 25 (x 0) (x 1)) = Signature.contract (closureKernel 25) (prepared 25) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_26 : (fun x : Fin 2 → Bool => outsideValues 26 (x 0) (x 1)) = Signature.contract (closureKernel 26) (prepared 26) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_27 : (fun x : Fin 2 → Bool => outsideValues 27 (x 0) (x 1)) = Signature.contract (closureKernel 27) (prepared 27) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_28 : (fun x : Fin 2 → Bool => outsideValues 28 (x 0) (x 1)) = Signature.contract (closureKernel 28) (prepared 28) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_29 : (fun x : Fin 2 → Bool => outsideValues 29 (x 0) (x 1)) = Signature.contract (closureKernel 29) (prepared 29) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_30 : (fun x : Fin 2 → Bool => outsideValues 30 (x 0) (x 1)) = Signature.contract (closureKernel 30) (prepared 30) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_31 : (fun x : Fin 2 → Bool => outsideValues 31 (x 0) (x 1)) = Signature.contract (closureKernel 31) (prepared 31) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_32 : (fun x : Fin 2 → Bool => outsideValues 32 (x 0) (x 1)) = Signature.contract (closureKernel 32) (prepared 32) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_36 : (fun x : Fin 2 → Bool => outsideValues 36 (x 0) (x 1)) = Signature.contract (closureKernel 36) (prepared 36) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_37 : (fun x : Fin 2 → Bool => outsideValues 37 (x 0) (x 1)) = Signature.contract (closureKernel 37) (prepared 37) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_38 : (fun x : Fin 2 → Bool => outsideValues 38 (x 0) (x 1)) = Signature.contract (closureKernel 38) (prepared 38) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_39 : (fun x : Fin 2 → Bool => outsideValues 39 (x 0) (x 1)) = Signature.contract (closureKernel 39) (prepared 39) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_40 : (fun x : Fin 2 → Bool => outsideValues 40 (x 0) (x 1)) = Signature.contract (closureKernel 40) (prepared 40) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_41 : (fun x : Fin 2 → Bool => outsideValues 41 (x 0) (x 1)) = Signature.contract (closureKernel 41) (prepared 41) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_42 : (fun x : Fin 2 → Bool => outsideValues 42 (x 0) (x 1)) = Signature.contract (closureKernel 42) (prepared 42) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_43 : (fun x : Fin 2 → Bool => outsideValues 43 (x 0) (x 1)) = Signature.contract (closureKernel 43) (prepared 43) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_44 : (fun x : Fin 2 → Bool => outsideValues 44 (x 0) (x 1)) = Signature.contract (closureKernel 44) (prepared 44) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_45 : (fun x : Fin 2 → Bool => outsideValues 45 (x 0) (x 1)) = Signature.contract (closureKernel 45) (prepared 45) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_46 : (fun x : Fin 2 → Bool => outsideValues 46 (x 0) (x 1)) = Signature.contract (closureKernel 46) (prepared 46) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact_47 : (fun x : Fin 2 → Bool => outsideValues 47 (x 0) (x 1)) = Signature.contract (closureKernel 47) (prepared 47) := by
  funext x
  obtain ⟨a,b,hx⟩ : ∃ a b, x=![a,b] := ⟨x 0,x 1,by funext j; fin_cases j <;> rfl⟩
  subst x
  cases a <;> cases b <;> decide +kernel
theorem outside_exact (j : Fin 48) (h : outsideRow j) : (fun x : Fin 2 → Bool => outsideValues j (x 0) (x 1))=Signature.contract (closureKernel j) (prepared j) := by
  fin_cases j
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · exact outside_exact_21
  · exact outside_exact_22
  · exact outside_exact_23
  · exact outside_exact_24
  · exact outside_exact_25
  · exact outside_exact_26
  · exact outside_exact_27
  · exact outside_exact_28
  · exact outside_exact_29
  · exact outside_exact_30
  · exact outside_exact_31
  · exact outside_exact_32
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · norm_num [outsideRow,rowForm,rowBase] at h
  · exact outside_exact_36
  · exact outside_exact_37
  · exact outside_exact_38
  · exact outside_exact_39
  · exact outside_exact_40
  · exact outside_exact_41
  · exact outside_exact_42
  · exact outside_exact_43
  · exact outside_exact_44
  · exact outside_exact_45
  · exact outside_exact_46
  · exact outside_exact_47
end Holant.Certificates.OctahedralSeparator
