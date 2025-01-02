use ark_ec::PrimeGroup;
use ark_ed_on_bls12_381_bandersnatch::Fr;
use ark_ff::{BigInteger, PrimeField, Zero};
use ark_std::vec::Vec;
use crate::Element;

/// A helper type that contains all the context required for computing
/// a window NAF multiplication of a PrimeGroup element by a scalar.
pub struct WnafContext {
    pub window_size: usize,
}

impl WnafContext {
    /// Constructs a new context for a window of size `window_size`.
    ///
    /// # Panics
    ///
    /// This function will panic if not `2 <= window_size < 64`
    pub fn new(window_size: usize) -> Self {
        assert!(window_size >= 2);
        assert!(window_size < 64);
        Self { window_size }
    }

    pub fn table<G: PrimeGroup>(&self, mut base: G) -> Vec<G> {
        let window_count = (256 + self.window_size - 1) / self.window_size; // 等价于 ceil(256 / self.window_size)
        let table_size = window_count * (1 << (self.window_size - 1));
        let mut table = Vec::with_capacity(table_size);
        let threshold = 1 << (self.window_size - 1);

        for _ in 0..window_count {
            // 初始化 current_base 为 base
            let mut current_base = base;
            // 遍历窗口中的元素,table中为G,2G,3G,...,2^(window_size-1)G
            table.push(current_base);
            for _ in 1..threshold {
                current_base += &base;
                // 将 current_base 添加到表中
                table.push(current_base);
            }
            //2^(window_size-1)G+2^(window_size-1)G=2^(window_size)G
            base = current_base + current_base;
        }
        // 返回预计算表
        table
    }

    /// Computes scalar multiplication of a PrimeGroup element `g` by `scalar`.
    ///
    /// This method uses the wNAF algorithm to perform the scalar
    /// multiplication; first, it uses `Self::table` to calculate an
    /// appropriate table of multiples of `g`, and then uses the wNAF
    /// algorithm to compute the scalar multiple.
    pub fn mul<G: PrimeGroup>(&self, g: G, scalar: &G::ScalarField) -> G {
        let table = self.table(g);
        self.mul_with_table(&table, scalar).unwrap()
    }

    pub fn mul_with_table<G: PrimeGroup>(&self, base_table: &[G], scalar: &G::ScalarField) -> Option<G> {
        // 检查 base_table 是否太小
        if 1 << (self.window_size - 1) > base_table.len() {
            return None;
        }
        // 将标量转换为 wNAF 数据
        let wnaf_data = WnafContext::scalar_to_wnaf_data::<G>(scalar, self.window_size);
        let pre_comp_size = 1 << (self.window_size - 1);
        let mut result = G::zero();
        // 遍历 wNAF 数据
        for (i, &wnaf_value) in wnaf_data.iter().enumerate() {
            if wnaf_value < 0 {
                let element = base_table[(-wnaf_value - 1) as usize + i * pre_comp_size];
                result -= element;
            } else if wnaf_value > 0 {
                // 计算正索引并更新结果
                let element = base_table[(wnaf_value - 1) as usize + i * pre_comp_size];
                result += element;
            }
        }
        // 返回结果
        Some(result)
    }


    fn scalar_to_wnaf_data<G: PrimeGroup>(scalar: &G::ScalarField, w: usize) -> Vec<i64> {

        // win_data
        let source = WnafContext::scalar_to_u64::<G>(scalar);
        let mut result = Vec::new();
        let mut bit_buffer = 0u64;
        let mut bits_in_buffer = 0;

        for &value in &source {
            if  bits_in_buffer!=0 {
                bit_buffer |= (value << bits_in_buffer) & ((1 << w) - 1);
                result.push(bit_buffer as i64);
                bit_buffer = value>>(w-bits_in_buffer);
                bits_in_buffer =64-(w-bits_in_buffer);
            }else {
                bit_buffer=value;
                bits_in_buffer = 64;
            }

            while bits_in_buffer >= w {
                result.push((bit_buffer & ((1 << w) - 1)) as i64 );
                bit_buffer >>= w;
                bits_in_buffer -= w;
            }
        }

        if bits_in_buffer > 0 {
            result.push(bit_buffer as i64 );
        }

        // Adjust the result according to the condition
        let threshold = 1 << (w-1);
        for i in 0..result.len() {
            if result[i] > threshold {
                if i + 1 < result.len() {
                    result[i + 1] += 1;
                } else {
                    result.push(1);
                }
                result[i] -= 1 << w;
            }
        }

        result
    }
    #[inline]
    fn scalar_to_u64<G: PrimeGroup>(scalar: &G::ScalarField) -> Vec<u64> {
        let b = scalar.into_bigint();
        let mut num = b.num_bits();
        num = if num & 63 == 0 {
            num >> 6
        } else {
            (num >> 6) + 1
        };

        let mut res = Vec::with_capacity(num as usize);
        res.extend_from_slice(&b.as_ref()[..num as usize]);
        res
    }
}
pub struct WnafGottiContext {
    pub t: usize,
    pub b: usize,
}


impl WnafGottiContext {
    pub fn new(t: usize,b: usize) -> Self {
        assert!(b >= 2);
        assert!(b < 64);
        Self { t,b }
    }
    fn fill_window<G: PrimeGroup>(&self, basis: &mut [G], table: &mut [G]) {
        // 如果 basis 数组为空
        if basis.is_empty() {
            // 将 table 数组填充为零元素
            for i in 0..table.len() {
                table[i] = G::zero();
            }
            return;
        }
        let l = table.len();
        // 递归调用 fill_window，传入去掉第一个元素的 basis 数组和 table 数组的前半部分
        self.fill_window(&mut basis[1..], &mut table[.. l/ 2]);
        // 遍历 table 数组的前半部分
        for i in 0..l / 2 {
            // 将 table 数组后半部分的对应元素设置为当前元素与 basis 数组第一个元素的和
            table[l / 2 + i] = table[i] + basis[0];
        }
    }



    pub fn mul<G: PrimeGroup>(&self, g: G, scalar: &G::ScalarField) -> G {
        let table = self.table(g);
        self.mul_with_table(&table, scalar).unwrap()
    }


    fn scalar_to_u64<G: PrimeGroup>(scalar: &G::ScalarField) -> Vec<u64> {
        let b = scalar.into_bigint();
        let mut num = b.num_bits();
        num = if num & 63 == 0 {
            num >> 6
        } else {
            (num >> 6) + 1
        };

        let mut res = Vec::with_capacity(num as usize);
        res.extend_from_slice(&b.as_ref()[..num as usize]);
        res
    }
    pub(crate) fn gotti_window<G: PrimeGroup>(&self, scalar: &G::ScalarField) -> Vec<Vec<u16>> {
        let b = scalar.into_bigint();
        let mut num = b.num_bits();
        num = if num & 63 == 0 {
            num >> 6
        } else {
            (num >> 6) + 1
        };
        let fr_bits = 253;
        let mut naf_vec: Vec<Vec<u8>> = vec![Vec::new(); self.t];

        let mut scalar_u64_4_ = Vec::with_capacity(num as usize);
        scalar_u64_4_.extend_from_slice(&b.as_ref()[..num as usize]);
        for t_i in 0..self.t {
            for k in (0..fr_bits).step_by(self.t) {
                let scalar_bit_pos = k + self.t - t_i - 1;
                // println!("k: {:?}", k);
                // println!("scalar_bit_pos: {:?}", scalar_bit_pos);
                if scalar_bit_pos < fr_bits && !scalar.is_zero() {
                    let limb = scalar_u64_4_[scalar_bit_pos >> 6];
                    let bit = ((limb >> (scalar_bit_pos & 63)) & 1) as u8;
                    naf_vec[t_i].push(bit);
                }
            }
        }
        let mut new_naf_vec: Vec<Vec<u16>> = Vec::with_capacity(self.t);

        for vec in naf_vec.iter() {
            let mut new_vec = Vec::with_capacity((vec.len() + self.b - 1) / self.b);
            let mut combined: u16 = 0;
            let mut bit_pos = 0;

            for &bit in vec.iter() {
                combined |= (bit as u16) << bit_pos;
                bit_pos += 1;

                if bit_pos == self.b {
                    new_vec.push(combined);
                    combined = 0;
                    bit_pos = 0;
                }
            }

            if bit_pos > 0 {
                new_vec.push(combined);
            }

            new_naf_vec.push(new_vec);
        }
        println!("new_naf_vec: {:?}", new_naf_vec);

        return new_naf_vec;
    }

    fn reverse_bits(&self,mut num: u32, t: usize) -> u32 {
        let mut reversed = 0;
        for _ in 0..t {
            reversed <<= 1;
            reversed |= num & 1;
            num >>= 1;
        }
        reversed
    }


    pub  fn rearrange_table<G: Clone>(&self,table: &[G]) -> Vec<G> {
        let mut table1 = vec![table[0].clone(); table.len()];
        for i in 0..table.len() {
            let reversed_index = self.reverse_bits(i as u32,self.b) as usize;
            table1[reversed_index] = table[i].clone();
        }
        table1
    }
    pub fn table<G: PrimeGroup>(&self,base: G)-> Vec<G> {

        let fr_bits =253;
        //b为窗口bit长度，t为预处理的倍数，window_size为每个窗口内的值的所有可能的值
        let window_size = 1 << self.b;
        //用t把标量分为t个部分，如果t=2，那么标量分为2部分，每部分的位数为fr_bits/2，kP=2A1+A0，
        // A1为高位，A0为低位，A1，A0即为划分出来的部分。A1、A0的所有可能的个数为points_per_column，
        // 如t=2，b=5，那么points_per_column=127
        let points_per_column = (fr_bits + self.t - 1) / self.t as usize;
        //窗口的个数
        let window_count = (points_per_column + self.b - 1) / self.b; // 等价于 ceil(256 / self.window_size)
        //let table_size = window_count * (1 << (self.b - 1));
        //let threshold = 1 << (self.b - 1);
        let mut table_basis = Vec::with_capacity(points_per_column);
        let mut dbl = base.clone();
        table_basis.push(base);
        //计算2^0*G,2^2*G,2^4*G,2^6*G,...,2^252*G
        for _i in 1..(points_per_column) {
            for _j in 0..self.t {
                dbl= dbl.double();
            }
            table_basis.push(dbl.clone());
        }
        let mut nn_table = vec![G::zero(); window_count * window_size];
        for i in 0..window_count {
            let w=i;
            let start = w * self.b as usize;
            let mut end = (w + 1) * self.b as usize;
            if end > table_basis.len() {
                end = table_basis.len();
            }
            let window_basis: &mut [G] = &mut table_basis[start..end];
            let mut table = vec![G::zero(); window_size];
            self.fill_window(window_basis, &mut *table);
            let  new_table=self.rearrange_table(&table);
            for (j, table_element) in new_table.into_iter().enumerate() {
                nn_table[w * window_size + j] = table_element;
            }
        }
        nn_table
    }
    pub fn mul_with_table<G: PrimeGroup>(&self, base_pre_table: &[G], mon_scalar: &G::ScalarField) -> Option<G> {
        if 1 << (self.b - 1) > base_pre_table.len() {
            return None;
        }

        let window_size = 1 << self.b;
        let mut accum = G::zero();
        let fr_bits = 253;
        let scalar_u64 = WnafGottiContext::scalar_to_u64::<G>(mon_scalar);

        for t_i in 0..self.t {
            if t_i > 0 {
                accum = accum.double();
            }

            let mut curr_window = 0;
            let mut window_scalar = 0;
            let mut window_bit_pos = 0;

            for k in (0..fr_bits).step_by(self.t) {
                let scalar_bit_pos = k + self.t - t_i - 1;

                if scalar_bit_pos < fr_bits && !mon_scalar.is_zero() {
                    let limb = scalar_u64[scalar_bit_pos >> 6];
                    let bit = (limb >> (scalar_bit_pos & 63)) & 1;
                    window_scalar |= (bit as usize) << (window_bit_pos);
                }

                window_bit_pos += 1;
                if window_bit_pos == self.b {
                    if window_scalar > 0 {
                        let window_precomp = &base_pre_table[curr_window * window_size..(curr_window + 1) * window_size];
                        accum += window_precomp[window_scalar];
                    }
                    curr_window += 1;
                    window_scalar = 0;
                    window_bit_pos = 0;
                }
            }

            if window_scalar > 0 {
                let window_slice = &base_pre_table[curr_window * window_size..(curr_window + 1) * window_size];
                accum += window_slice[window_scalar];
            }
        }

        Some(accum)
    }


}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::{try_reduce_to_element, msm_window::MSMPrecompWnaf, Element, Fr};

    use ark_std::rand::SeedableRng;
    use ark_std::UniformRand;
    use std::time::Instant;
    use rand_chacha::ChaCha20Rng;

    fn generate_random_elements(num_required_points: usize, seed: &'static [u8]) -> Vec<Element> {
        use sha2::{Digest, Sha256};

        let _choose_largest = false;

        // Hash the seed + i to get a possible x value
        let hash_to_x = |index: u64| -> Vec<u8> {
            let mut hasher = Sha256::new();
            hasher.update(seed);
            hasher.update(index.to_be_bytes());
            let bytes: Vec<u8> = hasher.finalize().to_vec();
            bytes
        };

        (0u64..)
            .map(hash_to_x)
            .filter_map(|hash_bytes| try_reduce_to_element(&hash_bytes))
            .take(num_required_points)
            .collect()
    }

    #[test]
    fn mertic_msm() {
        let g_base: Vec<_> = generate_random_elements(256, b"eth_verkle_oct_2021").into_iter().collect();

        let precomp = MSMPrecompWnaf::new(&g_base, 10);

        for num_loads in [32] {
            //let mut rng = rand::thread_rng();
            let mut rng = ChaCha20Rng::from_seed([0u8; 32]);
            /*let ax_array: Vec<Fr> = (0..256)
                .map(|i| {
                    if i < num_loads {
                        Fr::rand(&mut rng)
                    } else {
                        Fr::from(0)
                    }
                })
                .collect();

            let start = Instant::now();
            msm_by_array(&committer, &ax_array);
            let duration = start.elapsed();
            println!("msm_by_array({}) took: {:?}", num_loads, duration);*/

            let ax_array: Vec<(Fr, usize)> = (0..num_loads).map(|i| (Fr::rand(&mut rng), i)).collect();

            msm_by_delta(&precomp, &ax_array);

        }
    }

    fn msm_by_delta(c: &MSMPrecompWnaf, frs: &[(Fr, usize)]) -> Element {
        let start = Instant::now();
        let e = commit_sparse(c, frs.to_vec());
        let duration = start.elapsed();
        println!("msm_by_delta({}) took: {:?}", frs.len(), duration);
        e
    }

    fn commit_sparse(precomp: &MSMPrecompWnaf, val_indices: Vec<(Fr, usize)>) -> Element {
        let mut result = Element::zero();

        for (value, lagrange_index) in val_indices {
            result += precomp.mul_index(value, lagrange_index) //self.scalar_mul(value, lagrange_index)
        }
        result
    }
}
#[test]
fn correctness_precompute_one_table_test() {
    // Create a vector of 256 elements, each being a multiple of the prime subgroup generator
    // 创建一个包含 256 个元素的向量，每个元素都是素数子群生成元的倍数
    let mut basic_g = Vec::with_capacity(1);

    basic_g.push(Element::prime_subgroup_generator());
    let wnaf_gotti_context = WnafGottiContext::new(2,8);

    // Perform the operation
    let precompute = wnaf_gotti_context.table(basic_g[0].0);
    println!("precompute len: {:?}", precompute.len());

}