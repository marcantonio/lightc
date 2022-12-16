#[macro_export]
macro_rules! make_undef_value {
    ($ctx:expr, $ty:expr) => {
        match $ty {
            int8_types!() | Type::Char => $ctx.i8_type().get_undef().as_basic_value_enum(),
            int16_types!() => $ctx.i16_type().get_undef().as_basic_value_enum(),
            int32_types!() => $ctx.i32_type().get_undef().as_basic_value_enum(),
            int64_types!() => $ctx.i64_type().get_undef().as_basic_value_enum(),
            Type::Float => $ctx.f32_type().get_undef().as_basic_value_enum(),
            Type::Double => $ctx.f64_type().get_undef().as_basic_value_enum(),
            Type::Bool => $ctx.bool_type().get_undef().as_basic_value_enum(),
            Type::Void => $ctx.i8_type().get_undef().as_basic_value_enum(),
            Type::SArray(..) => todo!(),
            Type::Comp(_) => todo!(),
        }
    };
}

#[macro_export]
macro_rules! make_phi_for_type {
    ($bldr:expr, $ctx:expr, $ty:expr, $name:expr) => {
        match $ty {
            int8_types!() | Type::Char => $bldr.build_phi($ctx.i8_type(), &($name.to_owned() + ".int8")),
            int16_types!() => $bldr.build_phi($ctx.i16_type(), &($name.to_owned() + ".int16")),
            int32_types!() => $bldr.build_phi($ctx.i32_type(), &($name.to_owned() + ".int32")),
            int64_types!() => $bldr.build_phi($ctx.i64_type(), &($name.to_owned() + ".int64")),
            Type::Float => $bldr.build_phi($ctx.f32_type(), &($name.to_owned() + ".float")),
            Type::Double => $bldr.build_phi($ctx.f64_type(), &($name.to_owned() + ".double")),
            Type::Bool => $bldr.build_phi($ctx.bool_type(), &($name.to_owned() + ".bool")),
            Type::Void => $bldr.build_phi($ctx.i8_type(), &($name.to_owned() + ".void")),
            Type::SArray(..) => todo!(),
            Type::Comp(_) => todo!(),
        }
    };
}
