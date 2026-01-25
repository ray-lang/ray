//! Item path type for referring to definitions by their full path.

use serde::{Deserialize, Serialize};

use super::{ModulePath, Path};

/// An item path (FQN) identifies a specific definition within a module.
///
/// Examples: `core::int::add`, `myproject::utils::helper`, `mymodule::List::push`
///
/// Item paths are used for name resolution and cross-reference lookup.
/// An item path is a module path plus an item name (and possibly nested names for impl members).
///
/// For nested items like `List::push`:
/// - `module` would be `mymodule`
/// - `item` would be `["List", "push"]`
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ItemPath {
    /// The module path containing this item.
    pub module: ModulePath,
    /// The item name components, e.g., `["List", "push"]` for `List::push`.
    pub item: Vec<String>,
}

impl std::fmt::Display for ItemPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.module.is_empty() {
            write!(f, "{}", self.item.join("::"))
        } else {
            write!(f, "{}::{}", self.module, self.item.join("::"))
        }
    }
}

impl From<Path> for ItemPath {
    fn from(path: Path) -> Self {
        Self::from_path(&path).unwrap_or_else(|| Self {
            module: ModulePath::root(),
            item: vec![],
        })
    }
}

impl From<&Path> for ItemPath {
    fn from(path: &Path) -> Self {
        Self::from_path(path).unwrap_or_else(|| Self {
            module: ModulePath::root(),
            item: vec![],
        })
    }
}

impl From<&str> for ItemPath {
    fn from(value: &str) -> Self {
        let mut parts = value.split("::").collect::<Vec<_>>();
        if parts.is_empty() {
            return ItemPath::default();
        }

        if parts.len() == 1 {
            return ItemPath::new(ModulePath::root(), vec![parts[0].into()]);
        }

        let last = parts.pop().unwrap();
        ItemPath::new(
            ModulePath::new(parts.into_iter().map(String::from).collect()),
            vec![last.into()],
        )
    }
}

impl ItemPath {
    /// Create a new ItemPath from a module path and item name components.
    ///
    /// For simple items: `ItemPath::new(module, vec!["foo".into()])`
    /// For nested items: `ItemPath::new(module, vec!["List".into(), "push".into()])`
    pub fn new(module: impl Into<ModulePath>, item: Vec<String>) -> Self {
        Self {
            module: module.into(),
            item,
        }
    }

    /// Create an ItemPath from a full path.
    ///
    /// The last component becomes the item name, and everything before
    /// becomes the module path.
    ///
    /// Returns `None` if the path is empty.
    pub fn from_path(path: &Path) -> Option<Self> {
        let item = path.name()?;
        let module = ModulePath::from(path.parent());
        Some(Self {
            module,
            item: vec![item],
        })
    }

    /// Convert this ItemPath back to a full Path.
    pub fn to_path(&self) -> Path {
        let mut result = self.module.to_path();
        for component in &self.item {
            result = result.append(component);
        }
        result
    }

    /// Get the final item name (last component).
    pub fn item_name(&self) -> Option<&str> {
        self.item.last().map(|s| s.as_str())
    }

    /// Get the final item name (last component) defaulting to "".
    pub fn as_str(&self) -> &str {
        self.item.last().map(|s| s.as_str()).unwrap_or_default()
    }

    /// Get all item name components.
    pub fn item_components(&self) -> &[String] {
        &self.item
    }

    /// Check if this is a nested item path (e.g., `List::push`).
    pub fn is_nested(&self) -> bool {
        self.item.len() > 1
    }

    /// Get the parent item path for nested items.
    ///
    /// For `mymodule::List::push`, returns `mymodule::List`.
    /// For non-nested items, returns None.
    pub fn parent_item(&self) -> Option<ItemPath> {
        if self.item.len() <= 1 {
            return None;
        }
        let parent_items = self.item[..self.item.len() - 1].to_vec();
        Some(ItemPath {
            module: self.module.clone(),
            item: parent_items,
        })
    }

    /// Check if the path is empty
    pub fn is_empty(&self) -> bool {
        self.module.is_empty() && self.item.is_empty()
    }

    /// Create a new ItemPath with an additional item component appended.
    ///
    /// For example, if `self` is `mymodule::List` and we call `with_item("push")`,
    /// the result is `mymodule::List::push`.
    pub fn with_item(&self, name: &str) -> Self {
        let mut item = self.item.clone();
        item.push(name.to_string());
        Self {
            module: self.module.clone(),
            item,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::pathlib::{ItemPath, Path};

    #[test]
    fn item_path_from_path() {
        let path = Path::from("std::io::read");
        let item_path = ItemPath::from_path(&path).unwrap();

        assert_eq!(item_path.module.to_string(), "std::io");
        assert_eq!(item_path.item, vec!["read"]);
    }

    #[test]
    fn item_path_from_single_name() {
        let path = Path::from("foo");
        let item_path = ItemPath::from_path(&path).unwrap();

        assert!(item_path.module.is_empty());
        assert_eq!(item_path.item, vec!["foo"]);
    }

    #[test]
    fn item_path_to_path() {
        let item_path = ItemPath::new(Path::from("std::io"), vec!["read".into()]);
        let path = item_path.to_path();

        assert_eq!(path.to_string(), "std::io::read");
    }

    #[test]
    fn item_path_display() {
        let item_path = ItemPath::new(Path::from("std::io"), vec!["read".into()]);
        assert_eq!(item_path.to_string(), "std::io::read");

        let simple = ItemPath::new(Path::new(), vec!["foo".into()]);
        assert_eq!(simple.to_string(), "foo");
    }

    #[test]
    fn item_path_nested() {
        // For List::push in module mymodule
        let item_path = ItemPath::new(Path::from("mymodule"), vec!["List".into(), "push".into()]);

        assert_eq!(item_path.to_string(), "mymodule::List::push");
        assert_eq!(item_path.to_path().to_string(), "mymodule::List::push");
        assert!(item_path.is_nested());
        assert_eq!(item_path.item_name(), Some("push"));
    }

    #[test]
    fn item_path_parent_item() {
        let item_path = ItemPath::new(Path::from("mymodule"), vec!["List".into(), "push".into()]);

        let parent = item_path.parent_item().unwrap();
        assert_eq!(parent.to_string(), "mymodule::List");
        assert!(!parent.is_nested());
    }

    #[test]
    fn item_path_non_nested_has_no_parent() {
        let item_path = ItemPath::new(Path::from("mymodule"), vec!["foo".into()]);
        assert!(item_path.parent_item().is_none());
    }
}
