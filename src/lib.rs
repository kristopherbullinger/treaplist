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

    fn nth(&self, mut n: usize) -> Option<TreapKey> {
        if n > self.len() {
            return None;
        }
        let mut cur = self.root;
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

    fn split(&mut self, node: TreapKey, nth: usize) -> (TreapKey, TreapKey) {
        let (left, right) = match self.nodes.get(node) {
            Some(node) => (node.left, node.right),
            _ => return (TreapKey::null(), TreapKey::null()),
        };
        let left_count = self.count(left);
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
}
