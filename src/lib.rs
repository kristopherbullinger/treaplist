use rand::{rngs::ThreadRng, RngCore};
use slotmap::{Key as _, SlotMap};
use std::cmp::Ordering;
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
            count: 1, // self
        }
    }

    fn into_inner(self) -> T {
        self.value
    }
}

#[derive(Debug, Clone, Default)]
pub struct TreapList<T, RNG: RngCore = ThreadRng> {
    nodes: SlotMap<TreapKey, TreapNode<T>>,
    rng: RNG,
    root: TreapKey,
}

impl<T, RNG: RngCore> TreapList<T, RNG> {
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    fn nth(&self, n: usize) -> Option<TreapKey> {
        if n >= self.len() {
            return None;
        }
        let n = n + 1;
        let mut cur = self.root;
        loop {
            let TreapNode {
                left, right, count, ..
            } = self.nodes[cur];
            match count.cmp(&n) {
                Ordering::Greater => cur = left,
                Ordering::Equal => return Some(cur),
                Ordering::Less => cur = right,
            }
        }
    }

    pub fn get(&self, n: usize) -> Option<&T> {
        self.nth(n).map(|key| &self.nodes[key].value)
    }

    pub fn get_mut(&mut self, n: usize) -> Option<&mut T> {
        self.nth(n).map(|key| &mut self.nodes[key].value)
    }

    pub fn insert(&mut self, value: T, pos: usize) -> Option<TreapKey> {
        if self.len() < pos {
            return None;
        }
        let node = TreapNode::new(value, self.rng.next_u64());
        let key = self.nodes.insert(node);
        let (left, right) = self.split(self.root, pos);
        let left = self.merge(left, key);
        self.root = self.merge(left, right);
        self.nodes[self.root].parent = TreapKey::null();
        Some(key)
    }

    pub fn push(&mut self, value: T) -> TreapKey {
        self.insert(value, self.len()).unwrap()
    }

    fn count(&self, key: TreapKey) -> usize {
        self.nodes.get(key).map(|node| node.count).unwrap_or(0)
    }

    // fn position_of(&self, key: TreapKey) -> Option<usize> {
    //     let node = self.nodes.get(key)?;
    //     let mut pos = self.count(node.left);
    //     let mut prev = key;
    //     let mut cur = node.parent;
    //     while let Some(parent) = self.nodes.get(cur) {
    //         if parent.right == prev {
    //             pos += self.count(parent.left) + 1;
    //         }
    //         prev = cur;
    //         cur = parent.parent;
    //     }
    //     Some(pos)
    // }

    fn update(&mut self, key: TreapKey) {
        let (left, right) = match self.nodes.get(key) {
            Some(n) => (n.left, n.right),
            None => return,
        };
        let mut count = 1;
        if let Some(node) = self.nodes.get_mut(left) {
            node.parent = key;
            count += node.count;
        }
        if let Some(node) = self.nodes.get_mut(right) {
            node.parent = key;
            count += node.count;
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
            let (rl, rr) = self.split(right, nth - left_count - 1);
            self.nodes[node].right = rl;
            self.update(node);
            (node, rr)
        }
    }

    pub fn remove(&mut self, n: usize) -> Option<T> {
        None
    }

    pub fn remove_node(&mut self, key: TreapKey) -> Option<T> {
        let node = self.nodes.remove(key)?;
        let merged = self.merge(node.left, node.right);
        if let Some(parent) = self.nodes.get_mut(node.parent) {
            if parent.right == key {
                parent.right = merged;
            } else {
                parent.left = merged;
            }
            self.update(node.parent);
        }
        if key == self.root {
            self.root = merged;
            self.nodes[merged].parent = TreapKey::null();
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
