use ecow::EcoString;
use itertools::Itertools;
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::Arc;
use std::{collections::HashMap, marker::PhantomData};

use crate::wasm::encoder::WasmTypeDefinition;
use crate::wasm::environment::TypeBinding;

use super::encoder::WasmTypeImpl;
use super::environment::Environment;

/// A unique identifier parameterized by a type.
pub struct Id<T> {
    /// The index of the identifier.
    index: u32,

    _marker: PhantomData<T>,
}

impl<T> Id<T> {
    pub fn new(index: u32) -> Self {
        Self {
            index,
            _marker: PhantomData,
        }
    }

    pub fn id(&self) -> u32 {
        self.index
    }
}

// manual implementation of following traits
impl<T> PartialEq for Id<T> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<T> Eq for Id<T> {}

impl<T> Hash for Id<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Id<T> {}

impl<T> Debug for Id<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Id({})", self.index)
    }
}

impl<T> Default for Id<T> {
    fn default() -> Self {
        Self {
            index: 0,
            _marker: PhantomData,
        }
    }
}

/// Unique identifier for types.
pub type TypeId = Id<Type>;

/// Unique identifier for functions.
pub type FunctionId = Id<Function>;

/// Sum type identifier.
pub type SumId = Id<Sum>;

/// Product type identifier.
pub type ProductId = Id<Product>;

/// Constant identifier.
pub type ConstantId = Id<Constant>;

/// Local identifier
pub type LocalId = Id<Local>;

// bring over WasmType later.
pub type TypeDefinition = super::WasmType;

/// Represents a type in the type table.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Type {
    /// The unique identifier of the type.
    pub id: TypeId,

    /// The name of the type, for debugging purposes.
    pub name: EcoString,

    /// The definition of the type.
    pub definition: TypeDefinition,
}

/// Represents a function in the function table.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    /// The unique identifier of the function.
    pub id: FunctionId,

    /// The name of the function, for debugging purposes.
    pub name: EcoString,

    /// The function's type signature.
    pub signature: TypeId,

    /// Arity.
    pub arity: u32,
}

/// Represents a sum type in the type table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sum {
    /// The unique identifier of the sum type.
    pub id: SumId,

    /// The name of the sum type, for debugging purposes.
    pub name: EcoString,

    /// The type of the sum type. Used for runtime type checking.
    pub type_: TypeId,

    /// Whether the type is made public outside of its module.
    /// If it's public, its constructor is exported from the Wasm module.
    pub public: bool,

    /// Function which tests for equality between two instances of this sum type.
    pub equality_test: FunctionId,

    /// Common fields.
    pub common_fields: Vec<ProductField>,

    /// Field order (from gleam-order to canonical-order).
    pub gleam_to_canonical_id: HashMap<usize, usize>,
}

/// Represents a product type in the type table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Product {
    /// The unique identifier of the product type.
    pub id: ProductId,

    /// The variant's tag.
    pub tag: u32,

    /// The name of the product type, for debugging purposes.
    pub name: EcoString,

    /// The type of the product type. Used for runtime type checking.
    pub type_: TypeId,

    /// The parent sum type of the product type.
    pub parent: SumId,

    /// Whether the product type is a simple product (has no fields, has a singleton instance),
    /// or a composite product (has fields, has a constructor).
    pub kind: ProductKind,

    /// The constructor function index.
    pub constructor: FunctionId,

    /// All fields.
    pub fields: Vec<ProductField>,

    /// Field order (from gleam-order to wasm-order).
    pub gleam_to_canonical_id: HashMap<usize, usize>,
}

/// Represents a field in a product type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProductField {
    pub name: EcoString,
    pub type_: FieldType,
    pub index: usize,
}

/// Represents a field type.
// TODO: Remove this enum and use TypeId directly.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldType {
    /// A sum reference.
    Sum(SumId),

    /// A function reference.
    Function(u32),

    /// Integer
    Int,

    /// Float
    Float,

    /// Boolean
    Bool,

    /// String
    String,

    /// Unit
    Nil,
}

impl FieldType {
    // basically copied from WasmTypeImpl
    pub fn from_gleam_type(
        type_: Arc<crate::type_::Type>,
        env: &Environment<'_>,
        table: &SymbolTable,
    ) -> Self {
        use crate::type_::Type as GleamType;
        use crate::type_::TypeVar;

        fn resolve_type_name(name: &str, env: &Environment<'_>, table: &SymbolTable) -> FieldType {
            if let Some(binding) = env.get_type(name) {
                match binding {
                    TypeBinding::Sum(id) => FieldType::Sum(id),
                }
            } else {
                panic!("Unknown type name: {}", name)
            }
        }

        if type_.is_int() {
            Self::Int
        } else if type_.is_float() {
            Self::Float
        } else if type_.is_bool() {
            Self::Bool
        } else if type_.is_nil() {
            Self::Nil
        } else if type_.is_string() {
            Self::String
        } else {
            match type_.as_ref() {
                // TODO: handle modules
                GleamType::Named { name, module, .. } => resolve_type_name(name, env, table),
                GleamType::Var {
                    type_: type_var, ..
                } => {
                    let b = type_var.borrow();
                    if let TypeVar::Link { ref type_ } = *b {
                        Self::from_gleam_type(Arc::clone(type_), env, table)
                    } else {
                        unreachable!("unresolved type var: {type_var:?}")
                    }
                }
                GleamType::Fn { args, retrn } => {
                    // find call type

                    // HACK: if we're calling this, then we know there exists a function with this type
                    // so we can just grab the first one that matches... but we need to scan the whole list
                    // of functions to find it
                    // ugh...

                    let these_args = args
                        .iter()
                        .map(|t| WasmTypeImpl::from_gleam_type(Arc::clone(&t), env, table))
                        .collect_vec();
                    let this_return = WasmTypeImpl::from_gleam_type(Arc::clone(&retrn), env, table);

                    let mut function_type_id = None;
                    for function_type in table.types.as_list().into_iter() {
                        // the type matches if the parameters and return types match
                        let (parameters, returns) = match &function_type.definition.definition {
                            WasmTypeDefinition::Function {
                                parameters,
                                returns,
                            } => (parameters, returns),
                            _ => continue,
                        };

                        if parameters == &these_args && returns == &this_return {
                            function_type_id = Some(function_type.definition.id);
                            break;
                        }
                    }

                    let function_type_id =
                        function_type_id.expect("There exists a function with this type");

                    Self::Function(function_type_id)
                }
                GleamType::Tuple { elems } => todo!("Tuples not implemented yet"),
            }
        }
    }

    pub fn to_wasm_type(&self, table: &SymbolTable) -> WasmTypeImpl {
        match self {
            Self::Int => WasmTypeImpl::Int,
            Self::Float => WasmTypeImpl::Float,
            Self::Bool => WasmTypeImpl::Bool,
            Self::Nil => WasmTypeImpl::Nil,
            Self::Sum(sum_id) => {
                let sum = table.sums.get(*sum_id).unwrap();
                let sum_type = table.types.get(sum.type_).unwrap();
                WasmTypeImpl::StructRef(sum_type.definition.id)
            }
            Self::String => {
                let string_type = table
                    .types
                    .get(table.string_type.unwrap())
                    .unwrap()
                    .definition
                    .id;
                WasmTypeImpl::ArrayRef(string_type)
            }
            Self::Function(type_id) => WasmTypeImpl::FuncRef(*type_id),
        }
    }
}

/// The kind of a product type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProductKind {
    /// A simple product type. This product type has no fields and has a singleton instance stored as a constant.
    Simple {
        /// The constant identifier of the singleton instance.
        instance: ConstantId,
    },

    /// A composite product type.
    Composite,
}

/// Represents a constant in the constant table.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Constant {
    /// The unique identifier of the constant.
    pub id: ConstantId,

    /// The name of the constant, for debugging purposes.
    pub name: EcoString,
}

/// Represents a local variable in the local table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Local {
    /// The unique identifier of the local variable.
    pub id: LocalId,

    /// The name of the local variable, for debugging purposes.
    pub name: EcoString,

    /// Wasm type.
    pub wasm_type: WasmTypeImpl,
}

/// Represents a string in the string table.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GleamString {
    /// The unique identifier of the string.
    pub id: Id<GleamString>,

    /// The string value.
    pub value: EcoString,

    /// The data segment index.
    pub data_segment: u32,
}

#[derive(Debug, Clone)]
pub struct Store<T: Clone + Debug> {
    items: HashMap<Id<T>, T>,
    next: u32,
}

impl<T: Clone + Debug> Store<T> {
    pub fn new() -> Self {
        Self {
            items: HashMap::new(),
            next: 0,
        }
    }

    pub fn with_offset(offset: u32) -> Self {
        Self {
            items: HashMap::new(),
            next: offset,
        }
    }

    pub fn new_id(&mut self) -> Id<T> {
        let id = Id::new(self.next);
        self.next += 1;
        id
    }

    pub fn insert(&mut self, id: Id<T>, item: T) {
        _ = self.items.insert(id, item);
    }

    pub fn get(&self, id: Id<T>) -> Option<&T> {
        self.items.get(&id)
    }

    pub fn get_mut(&mut self, id: Id<T>) -> Option<&mut T> {
        self.items.get_mut(&id)
    }

    pub fn as_list(&self) -> Vec<T> {
        let mut lst = vec![];
        for i in 0..self.next {
            let id = Id::new(i);
            if let Some(item) = self.items.get(&id) {
                lst.push(item.clone());
            }
        }
        lst
    }
}

#[derive(Debug, Clone)]
pub struct SymbolTable {
    pub types: Store<Type>,
    pub functions: Store<Function>,
    pub sums: Store<Sum>,
    pub products: Store<Product>,
    pub constants: Store<Constant>,

    pub int_division: Option<TypeId>,
    pub float_division: Option<TypeId>,
    pub string_type: Option<TypeId>,

    pub wasi_fd_write: u32,

    pub string_equality_test: Option<FunctionId>,
    pub string_concat: Option<FunctionId>,
    pub string_substring: Option<FunctionId>,
    pub string_write_out: Option<FunctionId>,

    pub float_to_int: Option<FunctionId>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            types: Store::new(),
            functions: Store::with_offset(1), // for fd_write's import
            sums: Store::new(),
            products: Store::new(),
            constants: Store::new(),
            int_division: None,
            float_division: None,
            wasi_fd_write: 0, // hardcoded for now
            string_type: None,
            string_equality_test: None,
            string_concat: None,
            string_substring: None,
            string_write_out: None,
            float_to_int: None,
        }
    }
}

/// A store for allocating local variables.
pub type LocalStore = Store<Local>;

/// A store for allocating strings.
pub type StringStore = Store<GleamString>;

/// Structure for string lookups;
pub struct Strings {
    strings: HashMap<EcoString, Id<GleamString>>,
    store: StringStore,
}

impl Strings {
    pub fn new() -> Self {
        Self {
            strings: HashMap::new(),
            store: StringStore::new(),
        }
    }

    pub fn get_or_insert_data_segment(&mut self, value: &str) -> u32 {
        if let Some(id) = self.strings.get(value) {
            return self.store.get(*id).unwrap().data_segment;
        }

        let id = self.store.new_id();
        let data_segment = id.id();
        let gleam_string = GleamString {
            id,
            value: value.into(),
            data_segment,
        };
        self.store.insert(id, gleam_string);
        _ = self.strings.insert(value.into(), id);
        data_segment
    }

    pub fn as_list(&self) -> Vec<GleamString> {
        self.store.as_list()
    }
}
