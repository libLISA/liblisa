use std::fmt::Debug;
use std::ops::Index;

use itertools::Itertools;
use log::{debug, info};

use super::bitmap::GrowingBitmap;
use crate::utils::mcs::bfs::Bfs;

mod bfs;

/// A brute-force minimum covering set-finder.
#[derive(Debug)]
pub struct MinimumCoveringSet {
    chosen: Vec<usize>,
}

struct Decision {
    nums: Vec<usize>,
    map: GrowingBitmap,
}

impl Debug for Decision {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.nums, f)
    }
}

impl Index<usize> for Decision {
    type Output = usize;

    fn index(&self, index: usize) -> &Self::Output {
        &self.nums[index]
    }
}

impl Decision {
    pub fn new(nums: Vec<usize>) -> Self {
        Self {
            map: {
                let mut m = GrowingBitmap::new();
                for &num in nums.iter() {
                    m.set(num);
                }

                m
            },
            nums,
        }
    }

    pub fn contains(&self, index: usize) -> bool {
        self.map[index]
    }
}

impl MinimumCoveringSet {
    fn find_best_decisions(mut decisions: Vec<Vec<usize>>, num_choices: usize) -> Option<Vec<usize>> {
        info!("Decisions = {decisions:?}");
        decisions.sort();
        decisions.dedup();

        let mut decisions = decisions
            .into_iter()
            .map(|decision| {
                let mut map = GrowingBitmap::new_all_zeros(num_choices);
                for &n in decision.iter() {
                    map.set(n);
                }

                map
            })
            .collect::<Vec<_>>();

        let mut decided = GrowingBitmap::new();
        loop {
            let mut modified = false;
            let size_before = decisions.len();
            decisions.dedup();

            decisions.retain(|m| {
                if m.count_ones() == 1 {
                    decided.set(m.first_bit_set().unwrap());

                    false
                } else {
                    true
                }
            });

            modified |= size_before != decisions.len();

            // If we've already decided
            decisions.retain(|m| !decided.overlaps_with(m));
            debug!("We must keep: {:?}", decided.iter_one_indices().collect::<Vec<_>>());
            debug!("Remaining decisions: {decisions:?}");

            for index in (0..decisions.len()).rev() {
                let decision = &decisions[index];
                if let Some(smaller) = decisions[0..index]
                    .iter()
                    .chain(decisions[index + 1..].iter())
                    .find(|other| decision.is_superset_of(other))
                {
                    debug!("Removing {:?} because we also have {:?}", decision, smaller);
                    decisions.remove(index);
                }
            }

            let mut num = vec![0u64; num_choices];
            for decision in decisions.iter() {
                for n in decision.iter_one_indices() {
                    num[n] += 1;
                }
            }

            info!("Remaining decisions: {decisions:?}");
            let mut removal_mask = GrowingBitmap::new_all_ones(num_choices);
            for (index, &num) in num.iter().enumerate().rev() {
                if num == 1 {
                    debug!("{index} is always a bad choice, removing it");
                    removal_mask.reset(index);
                }
            }

            info!("Clearing decisions...");
            for decision in decisions.iter_mut() {
                let first_index = decision.first_bit_set().expect("No MCS found");
                modified |= decision.and_with(&removal_mask);

                if modified && decision.is_all_zeros() {
                    decision.set(first_index);
                }
            }

            info!("Done");

            if !modified {
                break
            }
        }

        let decisions = decisions.iter().collect::<Vec<_>>();
        info!("Reduced decisions = {decisions:?}");
        if decisions.is_empty() {
            return Some(decided.iter_one_indices().collect())
        }

        let mut remap = vec![usize::MAX; num_choices];
        let mut counter = 0;

        let mut all_choices = decisions.iter().flat_map(|d| d.iter_one_indices()).collect::<Vec<_>>();

        all_choices.sort();

        for item in all_choices {
            if remap[item] == usize::MAX {
                remap[item] = counter;
                counter += 1;
            }
        }

        let decisions = decisions
            .iter()
            .map(|decision| {
                let mut b = GrowingBitmap::new_all_zeros(counter);
                for index in decision.iter_one_indices() {
                    b.set(remap[index]);
                }

                b
            })
            .collect::<Vec<_>>();

        info!(
            "Remapped to: {}",
            decisions
                .iter()
                .map(|d| format!("[{:?}]", d.iter_one_indices().format(", ")))
                .format(", ")
        );

        let best = {
            info!("Running simple BFS...");

            // let h = Hypergraph::from_bitmaps(decisions.iter());
            // let mut mmcs = Mmcs::new(&h);
            // let smallest = mmcs.find_smallest();

            // let mut mmcs = Mmcs::new(&h);
            // mmcs.set_cutoff_size(smallest.len());
            // let best = mmcs.find_best();

            let decisions = decisions
                .iter()
                .map(|b| b.iter_one_indices().collect())
                .map(Decision::new)
                .collect::<Vec<_>>();

            let mut bfs = Bfs::new(&decisions, counter);
            let best = bfs.run();

            let mut best_bitmap = GrowingBitmap::new();
            for index in best {
                let original_index = remap.iter().position(|&new_index| new_index == index).unwrap();
                debug!("Mapping back to original indices: {index} => {original_index}");
                best_bitmap.set(original_index);
            }

            best_bitmap
        };

        let combined = &best | &decided;
        info!("Best = {best:?}, decided = {decided:?}, combined = {combined:?}");

        Some(combined.iter_one_indices().collect())
    }

    /// `decisions` is a vec of length N, where there are N items to be covered.
    /// Each entry in `decisions` is a vec containing the indices X of the choices (X < `num_choices`) that cover this item.
    /// In other words, at least one choice from each vec in `decisions` must be picked.
    pub fn of(decisions: Vec<Vec<usize>>, num_choices: usize) -> MinimumCoveringSet {
        if let Some(mut chosen) = Self::find_best_decisions(decisions, num_choices) {
            chosen.sort();
            MinimumCoveringSet {
                chosen,
            }
        } else {
            MinimumCoveringSet {
                chosen: (0..num_choices).collect(),
            }
        }
    }

    /// Returns true if `index` is in the minimum covering set.
    pub fn contains(&self, index: usize) -> bool {
        self.chosen.contains(&index)
    }

    /// Converts the minimum covering set into a list of indices.
    pub fn into_vec(self) -> Vec<usize> {
        self.chosen
    }
}

impl PartialEq<[usize]> for MinimumCoveringSet {
    fn eq(&self, other: &[usize]) -> bool {
        for &index in other.iter() {
            if !self.contains(index) {
                return false;
            }
        }

        for index in self.chosen.iter() {
            if !other.contains(index) {
                return false;
            }
        }

        true
    }
}

impl<const N: usize> PartialEq<[usize; N]> for MinimumCoveringSet {
    fn eq(&self, other: &[usize; N]) -> bool {
        self == other.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use test_log::test;

    use crate::utils::MinimumCoveringSet;

    #[test]
    pub fn decisions_must_be_fast1() {
        let decisions = vec![
            vec![2, 3],
            vec![2, 378],
            vec![3, 4],
            vec![3, 378],
            vec![4, 6],
            vec![4, 12],
            vec![4, 18],
            vec![4, 24],
            vec![4, 30],
            vec![4, 36],
            vec![4, 42],
            vec![4, 48],
            vec![4, 54],
            vec![4, 60],
            vec![4, 66],
            vec![4, 72],
            vec![4, 78],
            vec![4, 84],
            vec![4, 90],
            vec![4, 96],
            vec![4, 102],
            vec![4, 108],
            vec![4, 114],
            vec![4, 120],
            vec![4, 126],
            vec![4, 132],
            vec![4, 138],
            vec![4, 144],
            vec![4, 150],
            vec![4, 156],
            vec![4, 162],
            vec![4, 168],
            vec![4, 174],
            vec![4, 180],
            vec![4, 186],
            vec![4, 192],
            vec![4, 198],
            vec![4, 204],
            vec![4, 210],
            vec![4, 216],
            vec![4, 222],
            vec![4, 228],
            vec![4, 234],
            vec![4, 240],
            vec![4, 246],
            vec![4, 252],
            vec![4, 258],
            vec![4, 264],
            vec![4, 270],
            vec![4, 276],
            vec![4, 282],
            vec![4, 288],
            vec![4, 294],
            vec![4, 300],
            vec![4, 306],
            vec![4, 312],
            vec![4, 318],
            vec![4, 324],
            vec![4, 330],
            vec![4, 336],
            vec![4, 342],
            vec![4, 348],
            vec![4, 354],
            vec![4, 360],
            vec![4, 366],
            vec![4, 372],
            vec![6, 8],
            vec![6, 9],
            vec![8, 9],
            vec![12, 14],
            vec![12, 15],
            vec![14, 15],
            vec![18, 20],
            vec![18, 21],
            vec![20, 21],
            vec![24, 26],
            vec![24, 27],
            vec![26, 27],
            vec![30, 32],
            vec![30, 33],
            vec![32, 33],
            vec![36, 38],
            vec![36, 39],
            vec![38, 39],
            vec![42, 44],
            vec![42, 45],
            vec![44, 45],
            vec![48, 50],
            vec![48, 51],
            vec![50, 51],
            vec![54, 56],
            vec![54, 57],
            vec![56, 57],
            vec![60, 62],
            vec![60, 63],
            vec![62, 63],
            vec![66, 68],
            vec![66, 69],
            vec![68, 69],
            vec![72, 74],
            vec![72, 75],
            vec![74, 75],
            vec![78, 80],
            vec![78, 81],
            vec![80, 81],
            vec![84, 86],
            vec![84, 87],
            vec![86, 87],
            vec![90, 92],
            vec![90, 93],
            vec![92, 93],
            vec![96, 98],
            vec![96, 99],
            vec![98, 99],
            vec![102, 104],
            vec![102, 105],
            vec![104, 105],
            vec![108, 110],
            vec![108, 111],
            vec![110, 111],
            vec![114, 116],
            vec![114, 117],
            vec![116, 117],
            vec![120, 122],
            vec![120, 123],
            vec![122, 123],
            vec![126, 128],
            vec![126, 129],
            vec![128, 129],
            vec![132, 134],
            vec![132, 135],
            vec![134, 135],
            vec![138, 140],
            vec![138, 141],
            vec![140, 141],
            vec![144, 146],
            vec![144, 147],
            vec![146, 147],
            vec![150, 152],
            vec![150, 153],
            vec![152, 153],
            vec![156, 158],
            vec![156, 159],
            vec![158, 159],
            vec![162, 164],
            vec![162, 165],
            vec![164, 165],
            vec![168, 170],
            vec![168, 171],
            vec![170, 171],
            vec![174, 176],
            vec![174, 177],
            vec![176, 177],
            vec![180, 182],
            vec![180, 183],
            vec![182, 183],
            vec![186, 188],
            vec![186, 189],
            vec![188, 189],
            vec![192, 194],
            vec![192, 195],
            vec![194, 195],
            vec![198, 200],
            vec![198, 201],
            vec![200, 201],
            vec![204, 206],
            vec![204, 207],
            vec![206, 207],
            vec![210, 212],
            vec![210, 213],
            vec![212, 213],
            vec![216, 218],
            vec![216, 219],
            vec![218, 219],
            vec![222, 224],
            vec![222, 225],
            vec![224, 225],
            vec![228, 230],
            vec![228, 231],
            vec![230, 231],
            vec![234, 236],
            vec![234, 237],
            vec![236, 237],
            vec![240, 242],
            vec![240, 243],
            vec![242, 243],
            vec![246, 248],
            vec![246, 249],
            vec![248, 249],
            vec![252, 254],
            vec![252, 255],
            vec![254, 255],
            vec![258, 260],
            vec![258, 261],
            vec![260, 261],
            vec![264, 266],
            vec![264, 267],
            vec![266, 267],
            vec![270, 272],
            vec![270, 273],
            vec![272, 273],
            vec![276, 278],
            vec![276, 279],
            vec![278, 279],
            vec![282, 284],
            vec![282, 285],
            vec![284, 285],
            vec![288, 290],
            vec![288, 291],
            vec![290, 291],
            vec![294, 296],
            vec![294, 297],
            vec![296, 297],
            vec![300, 302],
            vec![300, 303],
            vec![302, 303],
            vec![306, 308],
            vec![306, 309],
            vec![308, 309],
            vec![312, 314],
            vec![312, 315],
            vec![314, 315],
            vec![318, 320],
            vec![318, 321],
            vec![320, 321],
            vec![324, 326],
            vec![324, 327],
            vec![326, 327],
            vec![330, 332],
            vec![330, 333],
            vec![332, 333],
            vec![336, 338],
            vec![336, 339],
            vec![338, 339],
            vec![342, 344],
            vec![342, 345],
            vec![344, 345],
            vec![348, 350],
            vec![348, 351],
            vec![350, 351],
            vec![354, 356],
            vec![354, 357],
            vec![356, 357],
            vec![360, 362],
            vec![360, 363],
            vec![362, 363],
            vec![366, 368],
            vec![366, 369],
            vec![368, 369],
            vec![372, 374],
            vec![372, 375],
            vec![374, 375],
        ];

        let result = MinimumCoveringSet::of(decisions, 379);

        assert_eq!(result.into_vec().len(), 126);
    }

    #[test]
    pub fn decisions_must_be_fast2() {
        let decisions = vec![(0..800_000).collect::<Vec<_>>(), (799_999..1_300_000).collect::<Vec<_>>()];

        let result = MinimumCoveringSet::of(decisions, 1_300_000);
        assert_eq!(result.into_vec().len(), 1);
    }

    #[test]
    pub fn should_return_smallest() {
        check_mcs(
            vec![
                vec![
                    1, 2, 4, 6, 8, 9, 10, 12, 14, 15, 19, 20, 22, 23, 31, 33, 35, 38, 40, 41, 42, 44, 46, 48, 50, 51, 53, 56, 57,
                    58, 59, 60, 61, 63, 65, 69, 70, 72, 76, 78, 79, 85,
                ],
                vec![
                    4, 17, 25, 26, 27, 28, 29, 30, 31, 33, 45, 46, 55, 56, 57, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75,
                    76, 77, 78, 79, 80, 81, 82, 85, 86,
                ],
                vec![
                    5, 6, 8, 11, 12, 25, 26, 28, 29, 32, 35, 36, 37, 38, 40, 43, 44, 45, 47, 48, 50, 52, 53, 56, 58, 59, 62, 63,
                    64, 65, 67, 69, 71, 72, 76, 79, 81, 82, 83, 85,
                ],
                vec![
                    2, 7, 8, 10, 15, 20, 23, 30, 31, 32, 34, 35, 36, 39, 40, 42, 45, 49, 50, 59, 61, 66, 67, 73, 77, 84, 85, 86,
                ],
                vec![
                    3, 9, 10, 11, 12, 16, 21, 24, 25, 26, 28, 33, 34, 35, 36, 41, 42, 43, 44, 51, 52, 53, 60, 61, 62, 63, 68, 74,
                    75, 76, 77, 78, 79, 81, 86,
                ],
                vec![
                    13, 14, 15, 16, 17, 22, 23, 24, 25, 26, 37, 38, 39, 40, 41, 42, 43, 44, 45, 54, 55, 57, 58, 59, 60, 61, 62,
                    63, 64, 65, 66, 67, 68, 70, 71, 72, 73, 74, 78, 79, 83, 84, 85, 86,
                ],
                vec![
                    18, 19, 20, 21, 22, 23, 24, 25, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64,
                    65, 66, 67, 68, 80, 81, 82, 83, 84, 85, 86,
                ],
            ],
            vec![vec![2, 25]],
        );
    }

    fn check_mcs(decisions: Vec<Vec<usize>>, solutions: Vec<Vec<usize>>) {
        let num_choices = decisions.iter().flat_map(|d| d.iter()).max().unwrap() + 1;

        let mcs = MinimumCoveringSet::of(decisions, num_choices);
        println!("Found: {mcs:?}");

        let result = mcs.into_vec();

        assert!(
            solutions.contains(&result),
            "Solution found: {result:?}; Accepted solutions: {solutions:?}"
        );
    }

    #[test]
    pub fn split_must_add_split_item() {
        // This will split on '6'
        check_mcs(
            vec![
                vec![0, 12],
                vec![2, 12],
                vec![4, 6],
                vec![8, 9],
                vec![0, 1, 2],
                vec![0, 1, 6],
                vec![4, 9, 16],
                vec![9, 15, 17],
                vec![13, 14, 17, 18],
                vec![8, 13, 15, 17, 18],
                vec![6, 8, 13, 14, 15, 16],
            ],
            vec![vec![0, 4, 9, 12, 13], vec![0, 6, 9, 12, 13], vec![0, 2, 4, 8, 17]],
        );
    }

    #[test]
    pub fn find_actual_mcs1() {
        check_mcs(
            vec![
                vec![2, 6],
                vec![0, 2, 6],
                vec![1, 2, 6],
                vec![0, 1, 2, 4, 5],
                vec![1, 3, 5, 6],
                vec![2, 3, 4],
            ],
            vec![vec![1, 2]],
        );
    }

    #[test]
    pub fn find_actual_mcs2() {
        check_mcs(
            vec![
                vec![1, 3, 5, 7, 10],
                vec![2, 3, 11, 12, 14, 16],
                vec![4, 5, 11, 13, 15],
                vec![6, 7, 12, 13, 17],
                vec![8, 14, 15, 18],
                vec![9, 10, 16, 17, 18],
            ],
            vec![
                vec![3, 13, 18],
                // vec![ 5, 14, 17 ],
                // vec![ 7, 15, 16 ],
            ],
        );
    }

    #[test]
    pub fn find_actual_mcs3() {
        check_mcs(
            vec![
                vec![1, 4, 6, 8, 11, 12],
                vec![3, 4, 13, 14, 16, 18, 21],
                vec![5, 6, 13, 15, 17, 22],
                vec![7, 8, 14, 15, 19],
                vec![9, 16, 17, 20, 23],
                vec![10, 11, 18, 19, 20, 24],
                vec![2, 12, 21, 22, 23, 24],
            ],
            vec![
                vec![4, 6, 19, 23],
                // vec![ 8, 11, 16, 22 ],
                // vec![ 4, 8, 17, 24 ],
                // vec![ 6, 8, 16, 24 ],
                // vec![ 8, 12, 17, 18 ],
            ],
        );
    }

    #[test]
    pub fn find_actual_mcs4() {
        check_mcs(
            vec![
                vec![
                    1, 3, 6, 8, 10, 13, 14, 16, 21, 23, 25, 27, 33, 34, 37, 41, 45, 47, 50, 53, 57, 61, 65, 69, 72, 75, 106, 112,
                    117, 124, 126, 136, 147, 151, 170, 182, 189, 204, 212, 219, 221,
                ],
                vec![
                    5, 6, 72, 78, 79, 81, 83, 86, 90, 94, 100, 104, 128, 133, 140, 152, 162, 175, 189, 190, 206, 222, 237, 239,
                    240, 242,
                ],
                vec![
                    7, 8, 78, 80, 82, 87, 91, 95, 105, 106, 129, 141, 151, 163, 176, 191, 207, 234, 235,
                ],
                vec![9, 10, 79, 80, 84, 92, 96, 107, 142, 198],
                vec![11, 81, 82, 85, 88, 93, 97, 101, 113, 118, 143, 153, 164, 177, 208],
                vec![
                    12, 13, 83, 84, 85, 89, 98, 108, 114, 119, 123, 124, 130, 134, 144, 154, 165, 178, 199, 209, 221, 232, 238,
                    241, 242,
                ],
                vec![
                    2, 14, 17, 19, 22, 24, 28, 38, 42, 46, 54, 58, 62, 66, 70, 76, 86, 87, 88, 89, 111, 112, 137, 171, 174, 201,
                    235, 240,
                ],
                vec![15, 16, 17, 90, 91, 92, 93, 99, 102, 109, 120, 131, 145, 155, 166, 179, 192],
                vec![
                    3, 18, 19, 25, 34, 47, 94, 95, 96, 97, 98, 99, 103, 110, 111, 112, 115, 121, 125, 132, 135, 146, 151, 156,
                    167, 180, 189, 193, 200, 210, 221, 223, 232, 233, 237,
                ],
                vec![20, 21, 22, 100, 101, 102, 103, 116, 157, 181, 194, 211, 224],
                vec![
                    4, 23, 24, 25, 29, 31, 35, 39, 43, 48, 51, 55, 59, 63, 67, 71, 77, 104, 105, 106, 107, 108, 109, 110, 111,
                    112, 117, 126, 136, 137, 147, 174, 182, 201, 212, 233, 234, 235, 238,
                ],
                vec![26, 27, 28, 29, 113, 114, 115, 116, 117, 122, 148, 158, 225],
                vec![30, 31, 118, 119, 120, 121, 122, 127, 159, 195, 213, 226],
                vec![32, 33, 34, 35, 123, 124, 125, 126, 127, 138, 183, 196, 214, 232],
                vec![
                    36, 37, 38, 39, 128, 129, 130, 131, 132, 139, 149, 160, 168, 174, 184, 197, 202, 215, 236,
                ],
                vec![
                    40, 41, 42, 43, 133, 134, 135, 136, 137, 138, 139, 150, 169, 170, 171, 185, 203, 204, 216, 233, 236,
                ],
                vec![
                    44, 45, 46, 47, 48, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 161, 172, 186, 205, 217, 227,
                    234, 235,
                ],
                vec![49, 50, 51, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 173, 187, 218],
                vec![
                    52, 53, 54, 55, 73, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 188, 219, 228, 236, 239,
                    241,
                ],
                vec![
                    56, 57, 58, 59, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 220, 229, 237,
                    238, 239, 242,
                ],
                vec![60, 61, 62, 63, 190, 191, 192, 193, 194, 195, 196, 197, 230],
                vec![64, 65, 66, 67, 198, 199, 200, 201, 202, 203, 204, 205],
                vec![
                    68, 69, 70, 71, 72, 73, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 231,
                    240, 241, 242,
                ],
                vec![74, 75, 76, 77, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231],
            ],
            vec![
                vec![34, 93, 116, 159, 198, 230, 235, 236, 242],
                // vec![ 34, 116, 118, 155, 198, 230, 235, 236, 242 ],
                // vec![ 92, 118, 151, 157, 196, 201, 225, 236, 242 ],
                // vec![ 92, 118, 151, 157, 174, 196, 204, 225, 242 ],
                // vec![ 92, 122, 151, 153, 196, 201, 224, 236, 242 ],
                // vec![ 92, 118, 151, 157, 174, 196, 203, 225, 242 ],
            ],
        );
    }

    #[test]
    pub fn nonoverlapping_should_pick_first() {
        check_mcs(vec![vec![0, 1], vec![2, 3]], vec![vec![0, 2]]);
    }

    #[test]
    pub fn limit_equivalent_exploration() {
        // Remapped to: [0, 2, 4], [0, 3, 5], [0, 5, 6], [1, 2, 6], [1, 3, 4], [2, 3, 4, 5], [3, 4, 6], [3, 5, 6]
        // Choice #0 (original=0): 00011111
        // Choice #1 (original=1): 11100111
        // Choice #2 (original=2): 01101011
        // Choice #3 (original=3): 10110000
        // Choice #4 (original=4): 01110001
        // Choice #5 (original=5): 10011010
        // Choice #6 (original=6): 11001100

        // We should try 4 after: 1. Not after 0, 2 or 3.

        check_mcs(
            vec![
                vec![0, 2, 4], // <= When this one has been covered, 4 = 3 so we should never explore 4.
                vec![1, 3, 4],
                vec![2, 3, 4, 5],
                vec![1, 2, 6],
                vec![3, 5, 6],
                vec![0, 5, 6],
                vec![0, 3, 5],
                vec![3, 4, 6],
            ],
            vec![vec![0, 1, 3]],
        );
    }
}
