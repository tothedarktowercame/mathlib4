import DarkTower.WarMachine.PolicyPosterior

namespace DarkTower.WarMachine.MachinePolicyPosteriorWitness

/- Generated from the bounded schema-27 production fixture. The reference
uses the declared raw-exponential normalization and never reads retained Q. -/

/-- The record's absent F_pi branch is the closed softmax branch of the general carrier. -/
theorem fAbsentBranchCompatibility {PolicyIndex : Type*} (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → DarkTower.WarMachine.Holes.ExpectedFreeEnergyValue)
    (tau : ℝ) (policies : List PolicyIndex)
    (hhabit : ∀ π, 0 < habit π) (htau : 0 < tau)
    (hne : policies ≠ []) (hnodup : policies.Nodup) :
    DarkTower.WarMachine.PolicyPosterior.softmaxWithFPi habit grade (fun _ => 0) tau policies
      hhabit htau hne hnodup =
      DarkTower.WarMachine.Holes.softmax Real.exp Real.log habit grade tau policies := by
  exact DarkTower.WarMachine.PolicyPosterior.softmaxWithFPi_zero habit grade tau policies
    hhabit htau hne hnodup

/-- Rank 1: retained posterior versus raw-exp carrier reference. -/
theorem coordinate001 : (4971256597298457 / 288230376151711744 : ℚ) = (621407074662307 / 36028797018963968 : ℚ) + (1 / 288230376151711744 : ℚ) ∧ |(1 / 288230376151711744 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 2: retained posterior versus raw-exp carrier reference. -/
theorem coordinate002 : (4874633881580923 / 576460752303423488 : ℚ) = (2437316940790461 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 3: retained posterior versus raw-exp carrier reference. -/
theorem coordinate003 : (4775528952394141 / 576460752303423488 : ℚ) = (1193882238098535 / 144115188075855872 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 4: retained posterior versus raw-exp carrier reference. -/
theorem coordinate004 : (2222313728778555 / 288230376151711744 : ℚ) = (8889254915114219 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 5: retained posterior versus raw-exp carrier reference. -/
theorem coordinate005 : (8822213025122271 / 1152921504606846976 : ℚ) = (8822213025122269 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 6: retained posterior versus raw-exp carrier reference. -/
theorem coordinate006 : (8822213025122271 / 1152921504606846976 : ℚ) = (8822213025122269 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 7: retained posterior versus raw-exp carrier reference. -/
theorem coordinate007 : (8642475404335285 / 1152921504606846976 : ℚ) = (8642475404335283 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 8: retained posterior versus raw-exp carrier reference. -/
theorem coordinate008 : (8601803592431383 / 1152921504606846976 : ℚ) = (4300901796215691 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 9: retained posterior versus raw-exp carrier reference. -/
theorem coordinate009 : (8575964941897279 / 1152921504606846976 : ℚ) = (2143991235474319 / 288230376151711744 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 10: retained posterior versus raw-exp carrier reference. -/
theorem coordinate010 : (4227966213498963 / 576460752303423488 : ℚ) = (2113983106749481 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 11: retained posterior versus raw-exp carrier reference. -/
theorem coordinate011 : (4226936818821359 / 576460752303423488 : ℚ) = (2113468409410679 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 12: retained posterior versus raw-exp carrier reference. -/
theorem coordinate012 : (4192597400503123 / 576460752303423488 : ℚ) = (2096298700251561 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 13: retained posterior versus raw-exp carrier reference. -/
theorem coordinate013 : (8361633196953919 / 1152921504606846976 : ℚ) = (8361633196953917 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 14: retained posterior versus raw-exp carrier reference. -/
theorem coordinate014 : (4132831403534095 / 576460752303423488 : ℚ) = (2066415701767047 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 15: retained posterior versus raw-exp carrier reference. -/
theorem coordinate015 : (4129504440479461 / 576460752303423488 : ℚ) = (8259008880958919 / 1152921504606846976 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 16: retained posterior versus raw-exp carrier reference. -/
theorem coordinate016 : (8213507540531775 / 1152921504606846976 : ℚ) = (4106753770265887 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 17: retained posterior versus raw-exp carrier reference. -/
theorem coordinate017 : (1023235941593647 / 144115188075855872 : ℚ) = (8185887532749175 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 18: retained posterior versus raw-exp carrier reference. -/
theorem coordinate018 : (2042993880742573 / 288230376151711744 : ℚ) = (8171975522970291 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 19: retained posterior versus raw-exp carrier reference. -/
theorem coordinate019 : (4083524471789233 / 576460752303423488 : ℚ) = (8167048943578465 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 20: retained posterior versus raw-exp carrier reference. -/
theorem coordinate020 : (508379779639255 / 72057594037927936 : ℚ) = (4067038237114039 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 21: retained posterior versus raw-exp carrier reference. -/
theorem coordinate021 : (4066785890564461 / 576460752303423488 : ℚ) = (8133571781128919 / 1152921504606846976 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 22: retained posterior versus raw-exp carrier reference. -/
theorem coordinate022 : (8094762870620253 / 1152921504606846976 : ℚ) = (4047381435310125 / 576460752303423488 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 23: retained posterior versus raw-exp carrier reference. -/
theorem coordinate023 : (1010286990464769 / 144115188075855872 : ℚ) = (4041147961859075 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 24: retained posterior versus raw-exp carrier reference. -/
theorem coordinate024 : (7984853746898553 / 1152921504606846976 : ℚ) = (998106718362319 / 144115188075855872 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 25: retained posterior versus raw-exp carrier reference. -/
theorem coordinate025 : (1993779731617921 / 288230376151711744 : ℚ) = (7975118926471683 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 26: retained posterior versus raw-exp carrier reference. -/
theorem coordinate026 : (991467531377137 / 144115188075855872 : ℚ) = (3965870125508547 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 27: retained posterior versus raw-exp carrier reference. -/
theorem coordinate027 : (3934449709941043 / 576460752303423488 : ℚ) = (1967224854970521 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 28: retained posterior versus raw-exp carrier reference. -/
theorem coordinate028 : (3911292458668955 / 576460752303423488 : ℚ) = (1955646229334477 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 29: retained posterior versus raw-exp carrier reference. -/
theorem coordinate029 : (3907849166129525 / 576460752303423488 : ℚ) = (976962291532381 / 144115188075855872 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 30: retained posterior versus raw-exp carrier reference. -/
theorem coordinate030 : (7765272766558281 / 1152921504606846976 : ℚ) = (7765272766558279 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 31: retained posterior versus raw-exp carrier reference. -/
theorem coordinate031 : (3849865576285997 / 576460752303423488 : ℚ) = (7699731152571993 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 32: retained posterior versus raw-exp carrier reference. -/
theorem coordinate032 : (3845833877519297 / 576460752303423488 : ℚ) = (60091154336239 / 9007199254740992 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 33: retained posterior versus raw-exp carrier reference. -/
theorem coordinate033 : (7684710287307501 / 1152921504606846976 : ℚ) = (7684710287307499 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 34: retained posterior versus raw-exp carrier reference. -/
theorem coordinate034 : (7683463715879001 / 1152921504606846976 : ℚ) = (7683463715878999 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 35: retained posterior versus raw-exp carrier reference. -/
theorem coordinate035 : (7630640973431279 / 1152921504606846976 : ℚ) = (7630640973431277 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 36: retained posterior versus raw-exp carrier reference. -/
theorem coordinate036 : (3785093554197553 / 576460752303423488 : ℚ) = (236568347137347 / 36028797018963968 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 37: retained posterior versus raw-exp carrier reference. -/
theorem coordinate037 : (3781511158612497 / 576460752303423488 : ℚ) = (7563022317224993 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 38: retained posterior versus raw-exp carrier reference. -/
theorem coordinate038 : (7541823986903433 / 1152921504606846976 : ℚ) = (3770911993451715 / 576460752303423488 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 39: retained posterior versus raw-exp carrier reference. -/
theorem coordinate039 : (7541823986903433 / 1152921504606846976 : ℚ) = (3770911993451715 / 576460752303423488 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 40: retained posterior versus raw-exp carrier reference. -/
theorem coordinate040 : (7541823986903433 / 1152921504606846976 : ℚ) = (3770911993451715 / 576460752303423488 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 41: retained posterior versus raw-exp carrier reference. -/
theorem coordinate041 : (7541823986903433 / 1152921504606846976 : ℚ) = (3770911993451715 / 576460752303423488 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 42: retained posterior versus raw-exp carrier reference. -/
theorem coordinate042 : (7541823986903433 / 1152921504606846976 : ℚ) = (3770911993451715 / 576460752303423488 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 43: retained posterior versus raw-exp carrier reference. -/
theorem coordinate043 : (7541823986903433 / 1152921504606846976 : ℚ) = (3770911993451715 / 576460752303423488 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 44: retained posterior versus raw-exp carrier reference. -/
theorem coordinate044 : (7529709666404349 / 1152921504606846976 : ℚ) = (7529709666404347 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 45: retained posterior versus raw-exp carrier reference. -/
theorem coordinate045 : (939990188111241 / 144115188075855872 : ℚ) = (7519921504889927 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 46: retained posterior versus raw-exp carrier reference. -/
theorem coordinate046 : (1874997765046713 / 288230376151711744 : ℚ) = (3749995530093425 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 47: retained posterior versus raw-exp carrier reference. -/
theorem coordinate047 : (7435560887685509 / 1152921504606846976 : ℚ) = (7435560887685507 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 48: retained posterior versus raw-exp carrier reference. -/
theorem coordinate048 : (7429689202236517 / 1152921504606846976 : ℚ) = (7429689202236515 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 49: retained posterior versus raw-exp carrier reference. -/
theorem coordinate049 : (7419100349920641 / 1152921504606846976 : ℚ) = (7419100349920639 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 50: retained posterior versus raw-exp carrier reference. -/
theorem coordinate050 : (7404028379883703 / 1152921504606846976 : ℚ) = (1851007094970925 / 288230376151711744 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 51: retained posterior versus raw-exp carrier reference. -/
theorem coordinate051 : (7384368695172307 / 1152921504606846976 : ℚ) = (7384368695172305 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 52: retained posterior versus raw-exp carrier reference. -/
theorem coordinate052 : (3678160819130255 / 576460752303423488 : ℚ) = (7356321638260507 / 1152921504606846976 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 53: retained posterior versus raw-exp carrier reference. -/
theorem coordinate053 : (7344242526552547 / 1152921504606846976 : ℚ) = (3672121263276273 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 54: retained posterior versus raw-exp carrier reference. -/
theorem coordinate054 : (1832297739164699 / 288230376151711744 : ℚ) = (7329190956658795 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 55: retained posterior versus raw-exp carrier reference. -/
theorem coordinate055 : (7328286769400333 / 1152921504606846976 : ℚ) = (7328286769400331 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 56: retained posterior versus raw-exp carrier reference. -/
theorem coordinate056 : (7302145126437029 / 1152921504606846976 : ℚ) = (7302145126437027 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 57: retained posterior versus raw-exp carrier reference. -/
theorem coordinate057 : (3649673786699033 / 576460752303423488 : ℚ) = (456209223337379 / 72057594037927936 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 58: retained posterior versus raw-exp carrier reference. -/
theorem coordinate058 : (7298827973095155 / 1152921504606846976 : ℚ) = (7298827973095153 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 59: retained posterior versus raw-exp carrier reference. -/
theorem coordinate059 : (1821556965146157 / 288230376151711744 : ℚ) = (7286227860584627 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 60: retained posterior versus raw-exp carrier reference. -/
theorem coordinate060 : (1818807112787821 / 288230376151711744 : ℚ) = (3637614225575641 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 61: retained posterior versus raw-exp carrier reference. -/
theorem coordinate061 : (908953823376933 / 144115188075855872 : ℚ) = (7271630587015463 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 62: retained posterior versus raw-exp carrier reference. -/
theorem coordinate062 : (906470144692051 / 144115188075855872 : ℚ) = (3625880578768203 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 63: retained posterior versus raw-exp carrier reference. -/
theorem coordinate063 : (7250799434341473 / 1152921504606846976 : ℚ) = (7250799434341471 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 64: retained posterior versus raw-exp carrier reference. -/
theorem coordinate064 : (3618346777451315 / 576460752303423488 : ℚ) = (1809173388725657 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 65: retained posterior versus raw-exp carrier reference. -/
theorem coordinate065 : (3618270507161369 / 576460752303423488 : ℚ) = (7236541014322737 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 66: retained posterior versus raw-exp carrier reference. -/
theorem coordinate066 : (7212731635024889 / 1152921504606846976 : ℚ) = (7212731635024887 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 67: retained posterior versus raw-exp carrier reference. -/
theorem coordinate067 : (7207670470060363 / 1152921504606846976 : ℚ) = (3603835235030181 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 68: retained posterior versus raw-exp carrier reference. -/
theorem coordinate068 : (7196314568314551 / 1152921504606846976 : ℚ) = (3598157284157275 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 69: retained posterior versus raw-exp carrier reference. -/
theorem coordinate069 : (7184201915269765 / 1152921504606846976 : ℚ) = (7184201915269763 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 70: retained posterior versus raw-exp carrier reference. -/
theorem coordinate070 : (3589264401097337 / 576460752303423488 : ℚ) = (7178528802194673 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 71: retained posterior versus raw-exp carrier reference. -/
theorem coordinate071 : (3586550333184341 / 576460752303423488 : ℚ) = (7173100666368681 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 72: retained posterior versus raw-exp carrier reference. -/
theorem coordinate072 : (7158886176149461 / 1152921504606846976 : ℚ) = (1789721544037365 / 288230376151711744 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 73: retained posterior versus raw-exp carrier reference. -/
theorem coordinate073 : (7128875454322409 / 1152921504606846976 : ℚ) = (7128875454322407 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 74: retained posterior versus raw-exp carrier reference. -/
theorem coordinate074 : (7116045350094021 / 1152921504606846976 : ℚ) = (1779011337523505 / 288230376151711744 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 75: retained posterior versus raw-exp carrier reference. -/
theorem coordinate075 : (7068165962277353 / 1152921504606846976 : ℚ) = (7068165962277351 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 76: retained posterior versus raw-exp carrier reference. -/
theorem coordinate076 : (3532306833614113 / 576460752303423488 : ℚ) = (110384588550441 / 18014398509481984 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 77: retained posterior versus raw-exp carrier reference. -/
theorem coordinate077 : (219418214058815 / 36028797018963968 : ℚ) = (7021382849882079 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 78: retained posterior versus raw-exp carrier reference. -/
theorem coordinate078 : (3507613220930319 / 576460752303423488 : ℚ) = (7015226441860635 / 1152921504606846976 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 79: retained posterior versus raw-exp carrier reference. -/
theorem coordinate079 : (7004338004408155 / 1152921504606846976 : ℚ) = (875542250551019 / 144115188075855872 : ℚ) + (3 / 1152921504606846976 : ℚ) ∧ |(3 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 80: retained posterior versus raw-exp carrier reference. -/
theorem coordinate080 : (1748416086135543 / 288230376151711744 : ℚ) = (3496832172271085 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 81: retained posterior versus raw-exp carrier reference. -/
theorem coordinate081 : (6935110178046047 / 1152921504606846976 : ℚ) = (3467555089023023 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 82: retained posterior versus raw-exp carrier reference. -/
theorem coordinate082 : (3466080669703331 / 576460752303423488 : ℚ) = (1733040334851665 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 83: retained posterior versus raw-exp carrier reference. -/
theorem coordinate083 : (3443848628870219 / 576460752303423488 : ℚ) = (6887697257740437 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 84: retained posterior versus raw-exp carrier reference. -/
theorem coordinate084 : (3443848628870219 / 576460752303423488 : ℚ) = (6887697257740437 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 85: retained posterior versus raw-exp carrier reference. -/
theorem coordinate085 : (3443848628870219 / 576460752303423488 : ℚ) = (6887697257740437 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 86: retained posterior versus raw-exp carrier reference. -/
theorem coordinate086 : (3443848628870219 / 576460752303423488 : ℚ) = (6887697257740437 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 87: retained posterior versus raw-exp carrier reference. -/
theorem coordinate087 : (3443848628870219 / 576460752303423488 : ℚ) = (6887697257740437 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 88: retained posterior versus raw-exp carrier reference. -/
theorem coordinate088 : (3443848628870219 / 576460752303423488 : ℚ) = (6887697257740437 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 89: retained posterior versus raw-exp carrier reference. -/
theorem coordinate089 : (3443848628870219 / 576460752303423488 : ℚ) = (6887697257740437 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 90: retained posterior versus raw-exp carrier reference. -/
theorem coordinate090 : (6873260669901733 / 1152921504606846976 : ℚ) = (1718315167475433 / 288230376151711744 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 91: retained posterior versus raw-exp carrier reference. -/
theorem coordinate091 : (6761814406355549 / 1152921504606846976 : ℚ) = (6761814406355549 / 1152921504606846976 : ℚ) + (0 : ℚ) ∧ |(0 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 92: retained posterior versus raw-exp carrier reference. -/
theorem coordinate092 : (6761814406355549 / 1152921504606846976 : ℚ) = (6761814406355549 / 1152921504606846976 : ℚ) + (0 : ℚ) ∧ |(0 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 93: retained posterior versus raw-exp carrier reference. -/
theorem coordinate093 : (6761814406355549 / 1152921504606846976 : ℚ) = (6761814406355549 / 1152921504606846976 : ℚ) + (0 : ℚ) ∧ |(0 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 94: retained posterior versus raw-exp carrier reference. -/
theorem coordinate094 : (104493668679705 / 18014398509481984 : ℚ) = (6687594795501119 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 95: retained posterior versus raw-exp carrier reference. -/
theorem coordinate095 : (6662538471138743 / 1152921504606846976 : ℚ) = (6662538471138741 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 96: retained posterior versus raw-exp carrier reference. -/
theorem coordinate096 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 97: retained posterior versus raw-exp carrier reference. -/
theorem coordinate097 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 98: retained posterior versus raw-exp carrier reference. -/
theorem coordinate098 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 99: retained posterior versus raw-exp carrier reference. -/
theorem coordinate099 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 100: retained posterior versus raw-exp carrier reference. -/
theorem coordinate100 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 101: retained posterior versus raw-exp carrier reference. -/
theorem coordinate101 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 102: retained posterior versus raw-exp carrier reference. -/
theorem coordinate102 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 103: retained posterior versus raw-exp carrier reference. -/
theorem coordinate103 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 104: retained posterior versus raw-exp carrier reference. -/
theorem coordinate104 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 105: retained posterior versus raw-exp carrier reference. -/
theorem coordinate105 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 106: retained posterior versus raw-exp carrier reference. -/
theorem coordinate106 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 107: retained posterior versus raw-exp carrier reference. -/
theorem coordinate107 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 108: retained posterior versus raw-exp carrier reference. -/
theorem coordinate108 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 109: retained posterior versus raw-exp carrier reference. -/
theorem coordinate109 : (1659394006245167 / 288230376151711744 : ℚ) = (6637576024980667 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 110: retained posterior versus raw-exp carrier reference. -/
theorem coordinate110 : (6631126362130315 / 1152921504606846976 : ℚ) = (3315563181065157 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 111: retained posterior versus raw-exp carrier reference. -/
theorem coordinate111 : (6539481088467419 / 1152921504606846976 : ℚ) = (3269740544233709 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 112: retained posterior versus raw-exp carrier reference. -/
theorem coordinate112 : (6539481088467419 / 1152921504606846976 : ℚ) = (3269740544233709 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 113: retained posterior versus raw-exp carrier reference. -/
theorem coordinate113 : (6539481088467419 / 1152921504606846976 : ℚ) = (3269740544233709 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 114: retained posterior versus raw-exp carrier reference. -/
theorem coordinate114 : (6539481088467419 / 1152921504606846976 : ℚ) = (3269740544233709 / 576460752303423488 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 115: retained posterior versus raw-exp carrier reference. -/
theorem coordinate115 : (1628744924950765 / 288230376151711744 : ℚ) = (6514979699803059 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 116: retained posterior versus raw-exp carrier reference. -/
theorem coordinate116 : (1628744924950765 / 288230376151711744 : ℚ) = (6514979699803059 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 117: retained posterior versus raw-exp carrier reference. -/
theorem coordinate117 : (1628744924950765 / 288230376151711744 : ℚ) = (6514979699803059 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 118: retained posterior versus raw-exp carrier reference. -/
theorem coordinate118 : (1628744924950765 / 288230376151711744 : ℚ) = (6514979699803059 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 119: retained posterior versus raw-exp carrier reference. -/
theorem coordinate119 : (1628744924950765 / 288230376151711744 : ℚ) = (6514979699803059 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 120: retained posterior versus raw-exp carrier reference. -/
theorem coordinate120 : (1628744924950765 / 288230376151711744 : ℚ) = (6514979699803059 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 121: retained posterior versus raw-exp carrier reference. -/
theorem coordinate121 : (1628744924950765 / 288230376151711744 : ℚ) = (6514979699803059 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 122: retained posterior versus raw-exp carrier reference. -/
theorem coordinate122 : (1628744924950765 / 288230376151711744 : ℚ) = (6514979699803059 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 123: retained posterior versus raw-exp carrier reference. -/
theorem coordinate123 : (1628744924950765 / 288230376151711744 : ℚ) = (6514979699803059 / 1152921504606846976 : ℚ) + (1 / 1152921504606846976 : ℚ) ∧ |(1 / 1152921504606846976 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 124: retained posterior versus raw-exp carrier reference. -/
theorem coordinate124 : (3197011237519627 / 576460752303423488 : ℚ) = (1598505618759813 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 125: retained posterior versus raw-exp carrier reference. -/
theorem coordinate125 : (3197011237519627 / 576460752303423488 : ℚ) = (1598505618759813 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 126: retained posterior versus raw-exp carrier reference. -/
theorem coordinate126 : (3197011237519627 / 576460752303423488 : ℚ) = (1598505618759813 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 127: retained posterior versus raw-exp carrier reference. -/
theorem coordinate127 : (3197011237519627 / 576460752303423488 : ℚ) = (1598505618759813 / 288230376151711744 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 128: retained posterior versus raw-exp carrier reference. -/
theorem coordinate128 : (2082202727747305 / 18014398509481984 : ℚ) = (4164405455494609 / 36028797018963968 : ℚ) + (1 / 36028797018963968 : ℚ) ∧ |(1 / 36028797018963968 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 129: retained posterior versus raw-exp carrier reference. -/
theorem coordinate129 : (6298298615770207 / 1152921504606846976 : ℚ) = (6298298615770205 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 130: retained posterior versus raw-exp carrier reference. -/
theorem coordinate130 : (6298298615770207 / 1152921504606846976 : ℚ) = (6298298615770205 / 1152921504606846976 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 131: retained posterior versus raw-exp carrier reference. -/
theorem coordinate131 : (784337607792079 / 144115188075855872 : ℚ) = (3137350431168315 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 132: retained posterior versus raw-exp carrier reference. -/
theorem coordinate132 : (784337607792079 / 144115188075855872 : ℚ) = (3137350431168315 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 133: retained posterior versus raw-exp carrier reference. -/
theorem coordinate133 : (784337607792079 / 144115188075855872 : ℚ) = (3137350431168315 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 134: retained posterior versus raw-exp carrier reference. -/
theorem coordinate134 : (784337607792079 / 144115188075855872 : ℚ) = (3137350431168315 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 135: retained posterior versus raw-exp carrier reference. -/
theorem coordinate135 : (784337607792079 / 144115188075855872 : ℚ) = (3137350431168315 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 136: retained posterior versus raw-exp carrier reference. -/
theorem coordinate136 : (784337607792079 / 144115188075855872 : ℚ) = (3137350431168315 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 137: retained posterior versus raw-exp carrier reference. -/
theorem coordinate137 : (784337607792079 / 144115188075855872 : ℚ) = (3137350431168315 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 138: retained posterior versus raw-exp carrier reference. -/
theorem coordinate138 : (784337607792079 / 144115188075855872 : ℚ) = (3137350431168315 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 139: retained posterior versus raw-exp carrier reference. -/
theorem coordinate139 : (784337607792079 / 144115188075855872 : ℚ) = (3137350431168315 / 576460752303423488 : ℚ) + (1 / 576460752303423488 : ℚ) ∧ |(1 / 576460752303423488 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 140: retained posterior versus raw-exp carrier reference. -/
theorem coordinate140 : (5946441132129583 / 2305843009213693952 : ℚ) = (2973220566064791 / 1152921504606846976 : ℚ) + (1 / 2305843009213693952 : ℚ) ∧ |(1 / 2305843009213693952 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 141: retained posterior versus raw-exp carrier reference. -/
theorem coordinate141 : (5882865359329925 / 2305843009213693952 : ℚ) = (1470716339832481 / 576460752303423488 : ℚ) + (1 / 2305843009213693952 : ℚ) ∧ |(1 / 2305843009213693952 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 142: retained posterior versus raw-exp carrier reference. -/
theorem coordinate142 : (363169310039441 / 144115188075855872 : ℚ) = (5810708960631055 / 2305843009213693952 : ℚ) + (1 / 2305843009213693952 : ℚ) ∧ |(1 / 2305843009213693952 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 143: retained posterior versus raw-exp carrier reference. -/
theorem coordinate143 : (497994776244625 / 110427941548649020598956093796432407239217743554726184882600387580788736 : ℚ) = (995989552489257 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) + (-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) ∧ |(-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 144: retained posterior versus raw-exp carrier reference. -/
theorem coordinate144 : (497994776244625 / 110427941548649020598956093796432407239217743554726184882600387580788736 : ℚ) = (995989552489257 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) + (-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) ∧ |(-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 145: retained posterior versus raw-exp carrier reference. -/
theorem coordinate145 : (497994776244625 / 110427941548649020598956093796432407239217743554726184882600387580788736 : ℚ) = (995989552489257 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) + (-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) ∧ |(-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 146: retained posterior versus raw-exp carrier reference. -/
theorem coordinate146 : (497994776244625 / 110427941548649020598956093796432407239217743554726184882600387580788736 : ℚ) = (995989552489257 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) + (-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) ∧ |(-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 147: retained posterior versus raw-exp carrier reference. -/
theorem coordinate147 : (497994776244625 / 110427941548649020598956093796432407239217743554726184882600387580788736 : ℚ) = (995989552489257 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) + (-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) ∧ |(-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Rank 148: retained posterior versus raw-exp carrier reference. -/
theorem coordinate148 : (497994776244625 / 110427941548649020598956093796432407239217743554726184882600387580788736 : ℚ) = (995989552489257 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) + (-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ) ∧ |(-7 / 220855883097298041197912187592864814478435487109452369765200775161577472 : ℚ)| ≤ (1 / 2^45 : ℚ) := by
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-- Maximum observed raw-exp versus retained binary64 residual; all 148 coordinates are bounded above by 2^-45. -/
theorem measuredMaximumResidual : (1 / 36028797018963968 : ℚ) ≤ (1 / 2^45 : ℚ) := by
  norm_num

end DarkTower.WarMachine.MachinePolicyPosteriorWitness

#print axioms DarkTower.WarMachine.MachinePolicyPosteriorWitness.fAbsentBranchCompatibility
#print axioms DarkTower.WarMachine.MachinePolicyPosteriorWitness.measuredMaximumResidual
