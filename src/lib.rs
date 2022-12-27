use rand::{rngs::ThreadRng, RngCore};
use slotmap::{Key as _, SlotMap};
use std::cmp::Ordering;
use std::collections::VecDeque;
slotmap::new_key_type! {
    pub struct TreapKey;
}

#[derive(Debug, Clone, Default)]
struct TreapNode<T> {
    value: T,
    priority: u64,
    left: TreapKey,
    right: TreapKey,
    parent: TreapKey,
    count: usize,
}

impl<T> TreapNode<T> {
    fn new(value: T, priority: u64) -> TreapNode<T> {
        TreapNode {
            value,
            priority,
            left: TreapKey::null(),
            right: TreapKey::null(),
            parent: TreapKey::null(),
            // how many nodes are beneath this one in the tree -- NOT its ordinal position
            count: 0,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TreapList<T, RNG: RngCore = ThreadRng> {
    nodes: SlotMap<TreapKey, TreapNode<T>>,
    rng: RNG,
    root: TreapKey,
}

impl<T, RNG: RngCore> TreapList<T, RNG> {
    pub fn new() -> Self
    where
        T: Default,
        RNG: Default,
    {
        Default::default()
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn clear(&mut self) {
        self.nodes.clear();
        self.root = TreapKey::null();
    }

    pub fn position(&self, key: TreapKey) -> Option<usize> {
        let node = self.nodes.get(key)?;
        let mut position = match self.nodes.get(node.left) {
            Some(leftnode) => leftnode.count + 1,
            _ => 0,
        };
        let mut cur = node.parent;
        let mut prev = key;
        while let Some(node) = self.nodes.get(cur) {
            if node.right == prev {
                let left_count = match self.nodes.get(node.left) {
                    Some(leftnode) => leftnode.count + 1,
                    _ => 0,
                };
                position += left_count;
                position += 1;
            }
            prev = cur;
            cur = node.parent;
        }
        Some(position)
    }

    fn max_height(&self) -> usize {
        let mut height = 0;
        let mut stack = VecDeque::new();
        stack.push_front((self.root, 0));
        while let Some((key, hgt)) = stack.pop_front() {
            height = height.max(hgt);
            if let Some(node) = self.nodes.get(key) {
                stack.push_back((node.left, hgt + 1));
                stack.push_back((node.right, hgt + 1));
            }
        }
        height
    }

    pub fn nth(&self, n: usize) -> Option<TreapKey> {
        self.nth_in_subtree(self.root, n)
    }

    fn nth_in_subtree(&self, root: TreapKey, mut n: usize) -> Option<TreapKey> {
        let count = self.nodes.get(root)?.count + 1;
        if n >= count {
            return None;
        }
        let mut cur = root;
        loop {
            let node = self.nodes.get(cur)?;
            let left_count = match self.nodes.get(node.left) {
                Some(lnode) => lnode.count + 1,
                None => 0,
            };
            match n.cmp(&left_count) {
                Ordering::Greater => {
                    n -= left_count;
                    n -= 1; //current node
                    cur = node.right;
                }
                Ordering::Equal => return Some(cur),
                Ordering::Less => {
                    cur = node.left;
                }
            }
        }
    }

    pub fn get(&self, n: usize) -> Option<&T> {
        self.nth(n).map(|key| &self.nodes[key].value)
    }

    pub fn get_mut(&mut self, n: usize) -> Option<&mut T> {
        self.nth(n).map(|key| &mut self.nodes[key].value)
    }

    pub fn get_node(&self, key: TreapKey) -> Option<&T> {
        self.nodes.get(key).map(|node| &node.value)
    }

    pub fn get_node_mut(&mut self, key: TreapKey) -> Option<&mut T> {
        self.nodes.get_mut(key).map(|node| &mut node.value)
    }

    fn insert_node(&mut self, node: TreapNode<T>, pos: usize) -> Option<TreapKey> {
        let key = self.nodes.insert(node);
        let (left, right) = self.split(self.root, pos);
        let left = self.merge(left, key);
        self.root = self.merge(left, right);
        self.nodes[self.root].parent = TreapKey::null();
        self.update(key);
        Some(key)
    }

    pub fn insert(&mut self, value: T, pos: usize) -> Option<TreapKey> {
        if self.len() < pos {
            return None;
        }
        let node = TreapNode::new(value, self.rng.next_u64());
        self.insert_node(node, pos)
    }

    pub fn push(&mut self, value: T) -> TreapKey {
        self.insert(value, self.len()).unwrap()
    }

    fn push_node(&mut self, node: TreapNode<T>) -> TreapKey {
        self.insert_node(node, self.len()).unwrap()
    }

    pub fn pop(&mut self) -> Option<T> {
        self.remove(self.len())
    }

    fn count(&self, key: TreapKey) -> usize {
        self.nodes.get(key).map(|node| node.count).unwrap_or(0)
    }

    // point the node's children to this one, and update the count of the current node
    fn update(&mut self, key: TreapKey) {
        let (left, right) = match self.nodes.get(key) {
            Some(n) => (n.left, n.right),
            None => return,
        };
        let mut count = 0;
        if let Some(node) = self.nodes.get_mut(left) {
            node.parent = key;
            count += node.count + 1;
        }
        if let Some(node) = self.nodes.get_mut(right) {
            node.parent = key;
            count += node.count + 1;
        }
        self.nodes[key].count = count;
    }

    fn merge(&mut self, left: TreapKey, right: TreapKey) -> TreapKey {
        if left.is_null() {
            return right;
        }
        if right.is_null() {
            return left;
        }
        if self.nodes[left].priority > self.nodes[right].priority {
            let lr = self.nodes[left].right;
            self.nodes[left].right = self.merge(lr, right);
            self.update(left);
            left
        } else {
            let rl = self.nodes[right].left;
            self.nodes[right].left = self.merge(left, rl);
            self.update(right);
            right
        }
    }

    fn split_iter(&mut self, node: TreapKey, nth: usize) -> (TreapKey, TreapKey) {
        let mut prev = match self.nth_in_subtree(node, nth) {
            Some(c) => c,
            _ => return (TreapKey::null(), TreapKey::null()),
        };
        let mut left = self.nodes[prev].left;
        let mut right = prev;
        self.nodes[prev].left = TreapKey::null();
        if let Some(node) = self.nodes.get_mut(left) {
            node.parent = TreapKey::null();
        }
        self.update(prev);
        let mut cur = self.nodes[prev].parent;
        loop {
            if cur == node {
                break;
            }
            let (cur_left, cur_right, parent) = {
                let node = &self.nodes[cur];
                (node.left, node.right, node.parent)
            };
            if cur_right == prev {
                self.nodes[cur].right = left;
                left = cur;
            } else if cur_left == prev {
                self.nodes[cur].left = right;
                right = cur;
            }
            self.update(cur);
            prev = cur;
            cur = parent;
        }

        (left, right)
    }

    fn split(&mut self, node: TreapKey, nth: usize) -> (TreapKey, TreapKey) {
        let (left, right) = match self.nodes.get(node) {
            Some(node) => (node.left, node.right),
            _ => return (TreapKey::null(), TreapKey::null()),
        };
        let left_count = match self.nodes.get(left) {
            Some(node) => node.count + 1,
            _ => 0,
        };
        if nth <= left_count {
            let (ll, lr) = self.split(left, nth);
            self.nodes[node].left = lr;
            self.update(node);
            (ll, node)
        } else {
            let (rl, rr) = self.split(right, nth - left_count);
            self.nodes[node].right = rl;
            self.update(node);
            (node, rr)
        }
    }

    pub fn remove(&mut self, n: usize) -> Option<T> {
        let key = self.nth(n)?;
        self.remove_node(key)
    }

    pub fn remove_node(&mut self, key: TreapKey) -> Option<T> {
        let node = self.nodes.remove(key)?;

        //update parent nodes' counts
        let mut cur = node.parent;
        while let Some(node) = self.nodes.get_mut(cur) {
            node.count -= 1;
            cur = node.parent;
        }

        let merged = self.merge(node.left, node.right);
        if let Some(parent_node) = self.nodes.get_mut(node.parent) {
            if parent_node.right == key {
                parent_node.right = merged;
            } else {
                parent_node.left = merged;
            }
            self.update(node.parent);
        }
        if key == self.root {
            self.root = merged;
        }

        Some(node.value)
    }

    pub fn iter(&self) -> Iter<'_, T> {
        let mut stack = VecDeque::new();
        stack.push_front(Item::Node(self.root));
        Iter {
            nodes: &self.nodes,
            stack,
        }
    }
}

#[derive(Debug)]
enum Item<T> {
    Node(TreapKey),
    Item(T),
}
pub struct Iter<'a, T> {
    stack: VecDeque<Item<&'a T>>,
    nodes: &'a SlotMap<TreapKey, TreapNode<T>>,
}

impl<'a, T: std::fmt::Debug> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let item = self.stack.pop_back()?;
            match item {
                Item::Node(key) => {
                    let node = match self.nodes.get(key) {
                        Some(node) => node,
                        None => {
                            if self.stack.is_empty() {
                                return None;
                            } else {
                                continue;
                            }
                        }
                    };
                    self.stack.push_back(Item::Node(node.right));
                    self.stack.push_back(Item::Item(&node.value));
                    self.stack.push_back(Item::Node(node.left));
                }
                Item::Item(val) => return Some(val),
            }
        }
    }
}

// pub struct IterMut<'a, T> {
//     stack: VecDeque<Item<&'a mut T>>,
//     nodes: &'a mut SlotMap<TreapKey, TreapNode<T>>,
// }

// impl<'a, T> Iterator for IterMut<'a, T> {
//     type Item = &'a mut T;
//     fn next(&mut self) -> Option<Self::Item> {
//         let stack_item = self.stack.pop_front()?;
//         loop {
//             match stack_item {
//                 Item::Node(key) => {
//                     let node = self.nodes.get_mut(key)?;
//                     self.stack.push_back(Item::Node(node.right));
//                     self.stack.push_back(Item::Item(&mut node.value));
//                     self.stack.push_back(Item::Node(node.left));
//                 }
//                 Item::Item(val) => return Some(val),
//             }
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert() {
        let mut tpl = TreapList::<u32>::new();
        for n in 0..10 {
            tpl.push(n);
        }
        for n in 0..10 {
            assert_eq!(tpl.get(n).copied(), Some(n as u32));
        }
        let five = tpl.remove(5);
        assert_eq!(five, Some(5));
        for n in 0..9 {
            let expected = if n >= 5 { n + 1 } else { n };
            assert_eq!(tpl.get(n).copied(), Some(expected as u32), "{:#?}", tpl);
        }
    }

    #[test]
    fn remove_all() {
        let mut tpl = TreapList::<u32>::new();
        for n in 0..10 {
            tpl.push(n);
        }
        for _ in 0..100 {
            tpl.pop();
        }
    }

    #[test]
    fn positions_1() {
        let mut list = TreapList::<u32>::new();
        let mut keys = vec![];
        let nodes = [(0, 0), (1, 2), (2, 1), (3, 3), (4, 4)];
        for (val, prio) in nodes.iter().copied() {
            let node = TreapNode::new(val, prio);
            let key = list.push_node(node);
            keys.push(key);
        }
        println!("{:#?}", list);
        for (i, key) in keys.iter().copied().enumerate() {
            assert_eq!(list.position(key), Some(i));
        }
    }

    #[test]
    fn positions_2() {
        let mut list = TreapList::<u32>::new();
        let mut keys = vec![];
        let nodes = [(0, 1), (1, 0), (2, 2), (3, 4), (4, 3)];
        for (val, prio) in nodes.iter().copied() {
            let node = TreapNode::new(val, prio);
            let key = list.push_node(node);
            keys.push(key);
        }
        println!("{:#?}", list);
        for (i, key) in keys.iter().copied().enumerate() {
            println!("i {}", i);
            let observed = list.position(key);
            let expected = Some(i);
            assert_eq!(
                observed, expected,
                "expected {:?}, got {:?}",
                expected, observed
            );
        }
    }

    #[test]
    fn rearrange() {
        let mut list = TreapList::<u32>::new();
        let mut keys = vec![];
        let nodes = [(0, 1), (1, 0), (2, 2), (3, 4), (4, 3)];
        for (val, prio) in nodes.iter().copied() {
            let node = TreapNode::new(val, prio);
            let key = list.push_node(node);
            keys.push(key);
        }
        list.remove(2);
        let sixty6 = list.push(66);
        println!("{:#?}", list);
        assert_eq!(list.position(sixty6), Some(list.len() - 1));
        for (i, key) in keys.iter().copied().enumerate() {
            let observed = list.position(key);
            if i == 2 {
                continue;
            } else if i > 2 {
                let expected = Some(i - 1);
                assert_eq!(
                    observed, expected,
                    "expected: {:?}, got {:?}",
                    expected, observed
                );
            } else {
                let expected = Some(i);
                assert_eq!(
                    observed, expected,
                    "expected: {:?}, got {:?}",
                    expected, observed
                );
            }
        }
    }

    #[test]
    fn split() {
        let ints = [(1i64, 78), (2, 89), (-3, 99)];
        let mut list = TreapList::<i64>::new();
        let keys = ints
            .iter()
            .copied()
            .map(|(int, prio)| {
                let node = TreapNode::new(int, prio);
                list.push_node(node)
            })
            .collect::<Vec<_>>();
        println!("{:#?}", list);
        assert_eq!(list.nth(1), Some(keys[1]));
        let (left, right) = list.split_iter(list.root, 1);
        assert_eq!(
            left, keys[0],
            "expected left: {:?}, got: {:?}",
            keys[0], left
        );
        assert_eq!(
            right, keys[1],
            "expected right: {:?}, got: {:?}",
            keys[1], right
        );
    }

    #[test]
    fn split_2() {
        let ints = [
            (1i64, 78),
            (2, 89),
            (-3, 99),
            (3, 55),
            (-2, 66),
            (0, 77),
            (4, 88),
        ];
        let mut list = TreapList::<i64>::new();
        let keys = ints
            .iter()
            .copied()
            .map(|(int, prio)| {
                let node = TreapNode::new(int, prio);
                list.push_node(node)
            })
            .collect::<Vec<_>>();
        for n in list.iter().copied() {
            println!("{}", n);
        }
        list.remove(0);
        let (left, right) = list.split(list.root, 1);
        assert_eq!(
            left, keys[1],
            "expected from split: {:?}, got {:?}",
            keys[1], left
        );
        assert_eq!(
            right, keys[2],
            "expected from split: {:?}, got {:?}",
            keys[2], right
        );
    }

    #[test]
    fn rearrange_2() {
        //         -3
        //      2      4
        //   1       0
        //         -2
        //        3
        // remove first item (1), reinsert at position 1, yielding...
        //         -3
        //      1      4
        //   2       0
        //         -2
        //        3
        let ints = [
            (1i64, 78),
            (2, 89),
            (-3, 99),
            (3, 55),
            (-2, 66),
            (0, 77),
            (4, 88),
        ];
        let mut list = TreapList::<i64>::new();
        list.remove(0);
        assert!(list.iter().copied().eq([2, -3, 3, -2, 0, 4,]));
        let node = TreapNode::new(ints[0].0, 70);
        list.insert_node(node, 1);
        assert!(list.iter().copied().eq([2, 1, -3, 3, -2, 0, 4,]));
    }
}
