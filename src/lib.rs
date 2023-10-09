//! 链表核心逻辑。维护链表的关联关系， 但不存储链表的具体数据， 数据有外部容器存储（该容器实现了Index<K, Output = Node<K, T>> + IndexMut<K, Output = Node<K, T>>）
//! 
//! 关于索引的意义，请参考：https://github.com/GaiaWorld/pi_lib/tree/master/dyn_uint
//! 由于需要从任意位置删除元素，我们未采用标准库使用vec作为双端队列内部容器的做法。
//! 如果要从任意位置删除，链表是个不错的选择。
//! 
//! 简单的使用本双端队列，请使用slab_deque模块提供的双端队列
//! 要查看本模块的用法，可以参照slab_deque模块，和https://github.com/GaiaWorld/pi_lib/tree/master/task_pool库

use std::marker::PhantomData;
use std::iter::Iterator;
use std::ops::{Index, IndexMut};

use derive_deref_rs::Deref;
use pi_null::Null;

/// 链表
#[derive(Debug)]
pub struct LinkList<K: Null + Copy + Eq, T, C: Index<K, Output = Node<K, T>> + IndexMut<K, Output = Node<K, T>>>{
	head : K,
	tail :K,
	len: usize,
	#[cfg(debug_assertions)]
	link_version: u32,

	mark: PhantomData<(T, C)>,
}

impl<K: Null + Copy + Eq, T, C: Index<K, Output = Node<K, T>> + IndexMut<K, Output = Node<K, T>>> Default for LinkList<K, T, C> {
	fn default() -> Self {
		LinkList::new()
	}
}

impl<K: Null + Copy + Eq, T, C: Index<K, Output = Node<K, T>> + IndexMut<K, Output = Node<K, T>>> LinkList<K, T, C> {
	pub fn new() -> Self {
		let mut buf = [0u8; 4];
		getrandom::getrandom(&mut buf).unwrap();
		Self {
			head: K::null(),
			tail: K::null(),
			len: 0,
			link_version: unsafe { *(buf.as_ptr() as usize as *mut u32) },
			mark: PhantomData,
		}
	}

	/// 取到头部节点
	pub fn head(&self) -> K {
		self.head
	}

	// 取到尾部节点
	pub fn tail(&self) -> K {
		self.tail
	}

	// 取到链表长度
	pub fn len(&self) -> usize {
		self.len
	}

	pub fn link_before_from(&mut self, link_key: K, anchor_key: K, container: &mut C, old_link: &mut Self) {
		// debug版本中，检查next_key是否是当前链表中的节点, 检查prev_key是否是old_link中的节点
		#[cfg(debug_assertions)] 
		if (!anchor_key.is_null() && container[anchor_key].link_version != self.link_version) || 
			(!link_key.is_null() && !container[link_key].link_version.is_null() && (container[link_key].link_version != old_link.link_version)) {
			panic!("{}",
				pi_print_any::out_any!(
					format, 
					"link_before fail, prev_key={:?}, next_key={:?}, link_version={:?}, prev_version={:?}, next_version={:?}", 
					link_key, anchor_key, self.link_version, container[link_key].link_version, container[link_key].link_version
				));
		}

		// 从旧的链表上移除
		old_link.remove_inner(link_key, container);
		
		// 插入到新的链表上
		self.link_before_inner(link_key, anchor_key, container);
	}


	/// 将目标节点设置在在锚点节点前面， 如果anchor_key为Null， 则插入到尾部
	/// 如果target_key或anchor_key不为Null， 必须保证在container中存在对应节点， 否则将panic
	pub fn link_before(&mut self, link_key: K, anchor_key: K, container: &mut C) {
		// debug版本中，检查next_key是否是当前链表中的节点, 检查prev_key是否已经在别的链表中（除了当前链表）
		#[cfg(debug_assertions)] 
		if (!anchor_key.is_null() && container[anchor_key].link_version != self.link_version) || 
			(!link_key.is_null() && !container[link_key].link_version.is_null() && (container[link_key].link_version != self.link_version)) {
			panic!("{}",
				pi_print_any::out_any!(
					format, 
					"link_before fail, prev_key={:?}, next_key={:?}, link_version={:?}, prev_version={:?}, next_version={:?}", 
					link_key, anchor_key, self.link_version, container[link_key].link_version, container[link_key].link_version
				));
		}

		// 从旧的链表上移除
		self.remove_inner(link_key, container);
		 
		self.link_before_inner(link_key, anchor_key, container);
	}

	// // 将目标节点设置在在锚点节点后面， 如果anchor_key为Null， 则插入到头部
	// /// 必须保证target_key对应的节点， prev、 next为Null，否在在debug版本中panic
	// pub fn link_after(&mut self, next_key: K, pre_key: K, container: &mut C) {
	// 	debug_assert!(container[next_key].prev.is_null() && container[next_key].next.is_null());

		
	// 	let next = if pre_key.is_null() {
	// 		let next = self.head;
	// 		self.head = next_key;
	// 		next
	// 	} else {
	// 		let anchor = &mut container[pre_key];
	// 		let next = anchor.next;
	// 		anchor.next = next_key;
	// 		next
	// 	};

	// 	if next.is_null() {
	// 		self.head = next_key;
	// 	} else {
	// 		container[next].prev = next_key;
	// 	}
	// 	self.len += 1;
	// }

	/// 从链表中移除节点（在从容器中移除之前调用此方法）
	pub fn remove(&mut self, key: K, container: &mut C){
		#[cfg(debug_assertions)] 
		if !key.is_null() && !container[key].link_version.is_null() && (container[key].link_version != self.link_version) {
			panic!("{}",
				pi_print_any::out_any!(
					format, 
					"remove fail, key={:?}, link_version={:?}, key_version={:?}", 
					key, self.link_version, container[key].link_version
				));
		}

		self.remove_inner(key, container);
		
	}

	// 清理该链表上的链接关系
	pub fn clear(&mut self, container: &mut C) {
		loop {
			if self.head.is_null() {
				self.tail = K::null();
				break;
			}
			let node = &mut container[self.head];

			self.head = node.next;
			node.next = K::null();
			node.prev = K::null();
		}
		self.len = 0;
	}

	pub fn iter<'a>(&self, container: &'a C) -> Iter<'a, K, T, C> {
		Iter{
			next: self.head,
			container: container,
			mark: PhantomData,
		}
	}

	pub fn keys<'a>(&self, container: &'a C) -> KeysIter<'a, K, T, C> {
		KeysIter{
			next: self.head,
			container: container,
			mark: PhantomData,
		}
	}

	fn link_before_inner(&mut self, link_key: K, anchor_key: K, container: &mut C) {
		let prev = if anchor_key.is_null() {
			let prev = self.tail;
			self.tail = link_key;
			prev
		} else {
			let next = &mut container[anchor_key];
			let prev = next.prev;
			// 后节点与当前节点建立连接关系
			next.prev = link_key;
			prev
		};

		if prev.is_null() {
			self.head = link_key;
		} else {
			// 前节点与前节点建立连接关系
			container[prev].next = link_key;
			
		}

		let node = &mut container[link_key];
		node.prev = prev;
		node.next = anchor_key;
		#[cfg(debug_assertions)] 
		{
			node.link_version = self.link_version;
		}

		self.len += 1;
	}

	fn remove_inner(&mut self, key: K, container: &mut C){
		let node = &mut container[key];
		let (prev, next) = (node.prev, node.next);
		node.prev = K::null();
		node.next = K::null();
		#[cfg(debug_assertions)] 
		{
			node.link_version = u32::null();
		}

		match (prev.is_null(), next.is_null()) {
			(true, true) => {
				//如果该元素既不存在上一个元素，也不存在下一个元素， 则设置队列的头部None， 且设置队列的尾部None
				if self.head == key {
					self.head = K::null();
					self.tail = K::null();
				} else {
					return;
				}
				// 如果self.head != node， 则说明链表中不止一个节点，当prev，next都为Null时， 证明node还为加入到链表中
			},
			
			(_, true) => {
				//如果该元素存在上一个元素，不存在下一个元素， 则将上一个元素的下一个元素设置为None, 并设置队列的尾部为该元素的上一个元素
				container[prev].next = K::null();
				self.tail = prev;
			},
			(true, _) => {
				//如果该元素不存在上一个元素，但存在下一个元素， 则将下一个元素的上一个元素设置为None, 并设置队列的头部为该元素的下一个元素
				container[next].prev = K::null();
				self.head = next;
			},
			(_, _) => {
				//如果该元素既存在上一个元素，也存在下一个元素， 则将上一个元素的下一个元素设置为本元素的下一个元素, 下一个元素的上一个元素设置为本元素的上一个元素
				container[prev].next = next;
				container[next].prev = prev;
			},
		}
		self.len -= 1;
	}


}

impl<K: Null + Clone + Copy + Eq, T, C: Index<K, Output = Node<K, T>> + IndexMut<K, Output = Node<K, T>>> Clone for LinkList<K, T, C>{
	fn clone(&self) -> LinkList<K, T, C>{
		LinkList {
			head: self.head,
			tail: self.tail,
			len: self.len,
			link_version: self.link_version,
			mark: PhantomData
		}
	}
}

pub struct KeysIter<'a, K: Null + Copy + 'static, T: 'a, C: 'a + Index<K, Output = Node<K, T>> + IndexMut<K, Output = Node<K, T>>> {
	next: K,
	container: &'a C,
	mark: PhantomData<T>
}

impl<'a, K: Null + Copy + 'static, T, C: Index<K, Output = Node<K, T>> + IndexMut<K, Output = Node<K, T>>> Iterator for KeysIter<'a, K, T, C> {
	type Item = K;

	fn next(&mut self) -> Option<K> {
		if self.next.is_null() {
			return None;
		}
		let next = self.next;
		let node = &self.container[next];
		self.next = node.next;
		Some(next)
	}
}

pub struct Iter<'a, K: Null + Copy + 'static, T: 'a, C: 'a + Index<K, Output = Node<K, T>> + IndexMut<K, Output = Node<K, T>>> {
	next: K,
	container: &'a C,
	mark: PhantomData<T>
}

impl<'a, K: Null + Copy + 'static, T, C: Index<K, Output = Node<K, T>> + IndexMut<K, Output = Node<K, T>>> Iterator for Iter<'a, K, T, C> {
	type Item = (K, &'a T);

	fn next(&mut self) -> Option<(K, &'a T)> {
		if self.next.is_null() {
			return None;
		}
		let next = self.next;
		let node = &self.container[next];
		self.next = node.next;
		Some((next, &node.elem))
	}
}

#[derive(Debug, Deref)]
pub struct Node<K: Null + Copy, T>{
	#[deref]
	pub(crate) elem: T,
	pub(crate) next: K,
	pub(crate) prev: K,
	#[cfg(debug_assertions)]
	pub(crate) link_version: u32,
}

impl<K: Null + Copy, T> Node<K, T> {
	pub fn new(elem: T) -> Self {
		Self {
			elem,
			next: K::null(),
			prev: K::null(),
			#[cfg(debug_assertions)]
			link_version: u32::null(),
		}
	}

	pub fn next(&self) -> K {
		self.next
	}

	pub fn prev(&self) -> K {
		self.prev
	}
}


#[cfg(test)]
mod test {
	use pi_slotmap::{SlotMap, Key, DefaultKey};

	use crate::{Node, LinkList};

	#[test]
	fn test() {
		let mut map: SlotMap<DefaultKey, Node<DefaultKey, usize>>  = SlotMap::default();
		let mut link_list = LinkList::new();

		/******************************************************************test link_before******************************************************************/
		// 从空容器开始插入第一个节点[k1]
		let k1 = map.insert(Node::new(1));
		link_list.link_before(k1, Key::null(), &mut map);
		assert_eq!(k1, link_list.head());
		assert_eq!(k1, link_list.tail());
		assert_eq!(1, link_list.len());
		let left = map.iter().map(|r| {(r.0, r.1.prev(), r.1.next())}).collect::<Vec<(DefaultKey, DefaultKey, DefaultKey)>>();
		let right = vec![
			(k1, DefaultKey::null(), DefaultKey::null())
		];
		assert_eq!(left, right);


		// 插入第二个节点[k1, k2]
		let k2 = map.insert(Node::new(2));
		link_list.link_before(k2, Key::null(), &mut map);
		assert_eq!(k1, link_list.head());
		assert_eq!(k2, link_list.tail());
		assert_eq!(2, link_list.len());
		let left = map.iter().map(|r| {(r.0, r.1.prev(), r.1.next())}).collect::<Vec<(DefaultKey, DefaultKey, DefaultKey)>>();
		let right = vec![
			(k1, DefaultKey::null(), k2),
			(k2, k1, DefaultKey::null())
		];
		assert_eq!(left, right);

		// 插入第三个节点在第二个节点之前[k1, k3, k2]
		let k3 = map.insert(Node::new(3));
		link_list.link_before(k3, k2, &mut map);
		assert_eq!(k1, link_list.head());
		assert_eq!(k2, link_list.tail());
		assert_eq!(3, link_list.len());
		let left = map.iter().map(|r| {(r.0, r.1.prev(), r.1.next())}).collect::<Vec<(DefaultKey, DefaultKey, DefaultKey)>>();
		let right = vec![
			(k1, DefaultKey::null(), k3),
			(k2, k3, DefaultKey::null()),
			(k3, k1, k2),
		];
		assert_eq!(left, right);


		// 插入第四个节点在第一个节点之前[k4, k1, k3, k2]
		let k4 = map.insert(Node::new(3));
		link_list.link_before(k4, k1, &mut map);
		assert_eq!(k4, link_list.head());
		assert_eq!(k2, link_list.tail());
		assert_eq!(4, link_list.len());
		let left = map.iter().map(|r| {(r.0, r.1.prev(), r.1.next())}).collect::<Vec<(DefaultKey, DefaultKey, DefaultKey)>>();
		let right = vec![
			(k1, k4, k3),
			(k2, k3, DefaultKey::null()),
			(k3, k1, k2),
			(k4, DefaultKey::null(), k1),
		];
		assert_eq!(left, right);


		/******************************************************************test remove******************************************************************/
		// 移除第三个节点[k4, k1, k2]
		link_list.remove(k3, &mut map);
		map.remove(k3);
		assert_eq!(k4, link_list.head());
		assert_eq!(k2, link_list.tail());
		assert_eq!(3, link_list.len());
		let left = map.iter().map(|r| {(r.0, r.1.prev(), r.1.next())}).collect::<Vec<(DefaultKey, DefaultKey, DefaultKey)>>();
		let right = vec![
			(k1, k4, k2),
			(k2, k1, DefaultKey::null()),
			(k4, DefaultKey::null(), k1),
		];
		assert_eq!(left, right);

		// 移除第四个节点[k1, k2]
		link_list.remove(k4, &mut map);
		map.remove(k4);
		assert_eq!(k1, link_list.head());
		assert_eq!(k2, link_list.tail());
		assert_eq!(2, link_list.len());
		let left = map.iter().map(|r| {(r.0, r.1.prev(), r.1.next())}).collect::<Vec<(DefaultKey, DefaultKey, DefaultKey)>>();
		let right = vec![
			(k1, DefaultKey::null(), k2),
			(k2, k1, DefaultKey::null()),
		];
		assert_eq!(left, right);

		// 移除第二个节点[k1]
		link_list.remove(k2, &mut map);
		map.remove(k2);
		assert_eq!(k1, link_list.head());
		assert_eq!(k1, link_list.tail());
		assert_eq!(1, link_list.len());
		let left = map.iter().map(|r| {(r.0, r.1.prev(), r.1.next())}).collect::<Vec<(DefaultKey, DefaultKey, DefaultKey)>>();
		let right = vec![
			(k1, DefaultKey::null(), DefaultKey::null())
		];
		assert_eq!(left, right);

		// 移除第一个节点[]
		link_list.remove(k1, &mut map);
		map.remove(k1);
		assert_eq!(DefaultKey::null(), link_list.head());
		assert_eq!(DefaultKey::null(), link_list.tail());
		assert_eq!(0, link_list.len());

	}
}


