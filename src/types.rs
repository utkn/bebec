use std::collections::HashMap;

use itertools::Itertools;

use crate::core::*;

/// A type that can be converted to/from values in a program.
pub trait Representible<'a>: Sized {
    fn try_from_val(val: Val<'a>) -> Option<Self>;
    fn to_val(self) -> Val<'a>;
}

macro_rules! create_tuple_impl {
    (($( $ts:tt ),+), ($( $ids:tt ),+)) => {
        impl<'a, $( $ts ),+> Representible<'a> for ($( $ts ),+,)
        where
        $( $ts : Representible<'a> ),+
        {
            fn try_from_val(val: Val<'a>) -> Option<Self> {
                let mut it = val.try_as_ordered_tuple()?.into_iter();
                Some(($( $ts::try_from_val(it.next()?)? ),+,))
            }

            fn to_val(self) -> Val<'a> {
                let vals = [
                    $( self.$ids.to_val() ),+
                ];
                Val::OrderedTuple(vals.into_iter().collect())
            }
        }
    };
}

create_tuple_impl!((T0), (0));
create_tuple_impl!((T0, T1), (0, 1));
create_tuple_impl!((T0, T1, T2), (0, 1, 2));
create_tuple_impl!((T0, T1, T2, T3), (0, 1, 2, 3));
create_tuple_impl!((T0, T1, T2, T3, T4), (0, 1, 2, 3, 4));
create_tuple_impl!((T0, T1, T2, T3, T4, T5), (0, 1, 2, 3, 4, 5));
create_tuple_impl!((T0, T1, T2, T3, T4, T5, T6), (0, 1, 2, 3, 4, 5, 6));
create_tuple_impl!((T0, T1, T2, T3, T4, T5, T6, T7), (0, 1, 2, 3, 4, 5, 6, 7));
create_tuple_impl!(
    (T0, T1, T2, T3, T4, T5, T6, T7, T8),
    (0, 1, 2, 3, 4, 5, 6, 7, 8)
);
create_tuple_impl!(
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9),
    (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)
);
create_tuple_impl!(
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10),
    (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
);
create_tuple_impl!(
    (T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11),
    (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11)
);

impl<'a> Representible<'a> for NamedTuple<'a> {
    fn try_from_val(val: Val<'a>) -> Option<Self> {
        val.try_as_named_tuple()
    }

    fn to_val(self) -> Val<'a> {
        Val::NamedTuple(self)
    }
}

impl<'a, T> From<T> for Val<'a>
where
    T: Representible<'a>,
{
    fn from(val: T) -> Self {
        val.to_val()
    }
}

impl<'a> Representible<'a> for OrderedTuple<'a> {
    fn try_from_val(val: Val<'a>) -> Option<Self> {
        val.try_as_ordered_tuple()
    }

    fn to_val(self) -> Val<'a> {
        Val::OrderedTuple(self)
    }
}

impl<'a> Representible<'a> for () {
    fn try_from_val(val: Val<'a>) -> Option<Self> {
        if val.is_nil() {
            Some(())
        } else {
            None
        }
    }

    fn to_val(self) -> Val<'a> {
        Val::nil()
    }
}

impl<'a> Representible<'a> for bool {
    fn try_from_val(val: Val<'a>) -> Option<Self> {
        val.unwrap_singular_tuple()
            .try_as_primitive()?
            .try_as_bool()
    }

    fn to_val(self) -> Val<'a> {
        Val::Primitive(Primitive::Bool(self))
    }
}

impl<'a> Representible<'a> for usize {
    fn try_from_val(val: Val<'a>) -> Option<Self> {
        val.unwrap_singular_tuple()
            .try_as_primitive()?
            .try_as_uint()
    }

    fn to_val(self) -> Val<'a> {
        Val::Primitive(Primitive::Uint(self))
    }
}

impl<'a> Representible<'a> for char {
    fn try_from_val(val: Val<'a>) -> Option<Self> {
        val.unwrap_singular_tuple()
            .try_as_primitive()?
            .try_as_char()
    }

    fn to_val(self) -> Val<'a> {
        Val::Primitive(Primitive::Char(self))
    }
}

impl<'a> Representible<'a> for String {
    fn try_from_val(val: Val<'a>) -> Option<Self> {
        val.unwrap_singular_tuple()
            .try_as_primitive()?
            .try_as_string()
    }

    fn to_val(self) -> Val<'a> {
        Val::Primitive(Primitive::String(self))
    }
}

impl<'a, T> Representible<'a> for Vec<T>
where
    T: Representible<'a>,
{
    fn try_from_val(val: Val<'a>) -> Option<Self> {
        let mut seq = Self::new();
        for v in val.try_as_ordered_tuple()? {
            seq.push(T::try_from_val(v)?);
        }
        Some(seq)
    }

    fn to_val(self) -> Val<'a> {
        Val::OrderedTuple(OrderedTuple::from_iter(self.into_iter().map_into()))
    }
}

impl<'a, T> Representible<'a> for HashMap<&'a str, T>
where
    T: Representible<'a>,
{
    fn try_from_val(val: Val<'a>) -> Option<Self> {
        let mut map = Self::new();
        for (k, v) in val.try_as_named_tuple()? {
            map.insert(k, T::try_from_val(v)?);
        }
        Some(map)
    }

    fn to_val(self) -> Val<'a> {
        Val::NamedTuple(NamedTuple::from_iter(
            self.into_iter().map(|(k, v)| (k, v.into())),
        ))
    }
}
