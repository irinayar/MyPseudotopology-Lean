import LeanCheck.TVGPlusModel

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGModel

def cs_m23_2_lo : List Nat := [1, 6, 197, 656, 335545, 430468, 687194768, 8472886095, 5629499534214, 1500946352969992, 184467440737095517, 66418035203011751425]

theorem blk_m23_2_lo : Lam [2,3] 100 66418035203011751424 = blockSum [2,3] 100 8 cs_m23_2_lo :=
  lam_blocks (S := [2,3]) (m := 100) (B := 8) (N := 66418035203011751424) (by decide) (by norm_num) (List.tail cs_m23_2_lo)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem val_m23_2_lo : blockSum [2,3] 100 8 cs_m23_2_lo < 1 := by decide +kernel

def cs_m23_2_hi : List Nat := [1, 6, 197, 656, 335545, 430468, 687194768, 8472886095, 5629499534214, 1500946352969992, 184467440737095517, 66547884734200435201]

theorem blk_m23_2_hi : Lam [2,3] 100 66547884734200435200 = blockSum [2,3] 100 8 cs_m23_2_hi :=
  lam_blocks (S := [2,3]) (m := 100) (B := 8) (N := 66547884734200435200) (by decide) (by norm_num) (List.tail cs_m23_2_hi)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem val_m23_2_hi : blockSum [2,3] 100 8 cs_m23_2_hi >= 1 := by decide +kernel

theorem Nstar_m23_2 : Lam [2,3] 100 66418035203011751424 < 1 /\ 1 <= Lam [2,3] 100 66547884734200435200 := by
  rw [blk_m23_2_lo, blk_m23_2_hi]
  exact ⟨val_m23_2_lo, val_m23_2_hi⟩

end TVGModel
end LeanCheck
