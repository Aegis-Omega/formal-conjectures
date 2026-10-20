import CvSFrequencyIntervalV1
example : ((116142 : ℚ) - 57430) / 65536 = 7339 / 8192 := by norm_num
example : (0 : ℚ) < 7339 / 8192 := by norm_num
example : ((116142 : ℚ) - 46688) / 65536 = 34727 / 32768 := by norm_num
example : (0 : ℚ) < 34727 / 32768 := by norm_num
example : (1208196817027810721792 : ℤ) - 873002480980930375314 =
    335194336046880346478 := by norm_num
example : (301 : ℕ) * 301 * (2 * 2^128 * (2 * 2^128)) < 2^280 := by decide +kernel
