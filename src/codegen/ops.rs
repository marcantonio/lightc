use inkwell::{values::BasicValueEnum, FloatPredicate};

use super::*;

impl<'a, 'ctx> Codegen<'a, 'ctx> {
    // Binary operations

    pub(super) fn add(
        &self,
        lhs: (BasicValueEnum<'ctx>, Type),
        rhs: (BasicValueEnum<'ctx>, Type),
    ) -> ExprResult<'ctx> {
        match lhs.1 {
            int_types!() => Ok(self
                .builder
                .build_int_add(lhs.0.into_int_value(), rhs.0.into_int_value(), "add.int")
                .as_basic_value_enum()),
            float_types!() => Ok(self
                .builder
                .build_float_add(
                    lhs.0.into_float_value(),
                    rhs.0.into_float_value(),
                    "add.float",
                )
                .as_basic_value_enum()),
            _ => Err("Unsupported type in `add` operation".to_string()),
        }
    }

    pub(super) fn sub(
        &self,
        lhs: (BasicValueEnum<'ctx>, Type),
        rhs: (BasicValueEnum<'ctx>, Type),
    ) -> ExprResult<'ctx> {
        match lhs.1 {
            int_types!() => Ok(self
                .builder
                .build_int_sub(lhs.0.into_int_value(), rhs.0.into_int_value(), "sub.int")
                .as_basic_value_enum()),
            float_types!() => Ok(self
                .builder
                .build_float_sub(
                    lhs.0.into_float_value(),
                    rhs.0.into_float_value(),
                    "sub.float",
                )
                .as_basic_value_enum()),
            _ => Err("Unsupported type in `subtract` operation".to_string()),
        }
    }

    pub(super) fn mul(
        &self,
        lhs: (BasicValueEnum<'ctx>, Type),
        rhs: (BasicValueEnum<'ctx>, Type),
    ) -> ExprResult<'ctx> {
        match lhs.1 {
            int_types!() => Ok(self
                .builder
                .build_int_mul(lhs.0.into_int_value(), rhs.0.into_int_value(), "mul.int")
                .as_basic_value_enum()),
            float_types!() => Ok(self
                .builder
                .build_float_mul(
                    lhs.0.into_float_value(),
                    rhs.0.into_float_value(),
                    "mul.float",
                )
                .as_basic_value_enum()),
            _ => Err("Unsupported type in `multiply` operation".to_string()),
        }
    }

    pub(super) fn div(
        &self,
        lhs: (BasicValueEnum<'ctx>, Type),
        rhs: (BasicValueEnum<'ctx>, Type),
    ) -> ExprResult<'ctx> {
        match lhs.1 {
            signed_int_types!() => Ok(self
                .builder
                .build_int_signed_div(lhs.0.into_int_value(), rhs.0.into_int_value(), "div.int")
                .as_basic_value_enum()),
            unsigned_int_types!() => Ok(self
                .builder
                .build_int_unsigned_div(lhs.0.into_int_value(), rhs.0.into_int_value(), "div.uint")
                .as_basic_value_enum()),
            float_types!() => Ok(self
                .builder
                .build_float_div(
                    lhs.0.into_float_value(),
                    rhs.0.into_float_value(),
                    "div.float",
                )
                .as_basic_value_enum()),
            _ => Err("Unsupported type in `divide` operation".to_string()),
        }
    }

    pub(super) fn and(
        &self,
        lhs: (BasicValueEnum<'ctx>, Type),
        rhs: (BasicValueEnum<'ctx>, Type),
    ) -> ExprResult<'ctx> {
        match lhs.1 {
            Type::Bool => Ok(self
                .builder
                .build_and(lhs.0.into_int_value(), rhs.0.into_int_value(), "and.int")
                .as_basic_value_enum()),
            _ => Err("Unsupported type in `and` operation".to_string()),
        }
    }

    pub(super) fn or(
        &self,
        lhs: (BasicValueEnum<'ctx>, Type),
        rhs: (BasicValueEnum<'ctx>, Type),
    ) -> ExprResult<'ctx> {
        match lhs.1 {
            Type::Bool => Ok(self
                .builder
                .build_or(lhs.0.into_int_value(), rhs.0.into_int_value(), "or.int")
                .as_basic_value_enum()),
            _ => Err("Unsupported type in `or` operation".to_string()),
        }
    }

    pub(super) fn cmp(
        &self,
        op: Symbol,
        lhs: (BasicValueEnum<'ctx>, Type),
        rhs: (BasicValueEnum<'ctx>, Type),
    ) -> ExprResult<'ctx> {
        use Symbol::*;

        let inst = match (lhs.1, op) {
            (int_types!() | Type::Bool | Type::Char, Eq) => self.builder.build_int_compare(
                IntPredicate::EQ,
                lhs.0.into_int_value(),
                rhs.0.into_int_value(),
                "eq.int",
            ),
            (signed_int_types!(), Gt) => self.builder.build_int_compare(
                IntPredicate::SGT,
                lhs.0.into_int_value(),
                rhs.0.into_int_value(),
                "sgt.int",
            ),
            (signed_int_types!(), Lt) => self.builder.build_int_compare(
                IntPredicate::SLT,
                lhs.0.into_int_value(),
                rhs.0.into_int_value(),
                "slt.int",
            ),
            (unsigned_int_types!() | Type::Char, Gt) => self.builder.build_int_compare(
                IntPredicate::UGT,
                lhs.0.into_int_value(),
                rhs.0.into_int_value(),
                "ugt.int",
            ),
            (unsigned_int_types!() | Type::Char, Lt) => self.builder.build_int_compare(
                IntPredicate::ULT,
                lhs.0.into_int_value(),
                rhs.0.into_int_value(),
                "ult.int",
            ),
            (float_types!(), Eq) => self.builder.build_float_compare(
                FloatPredicate::UEQ,
                lhs.0.into_float_value(),
                rhs.0.into_float_value(),
                "ueq.float",
            ),
            (float_types!(), Gt) => self.builder.build_float_compare(
                FloatPredicate::UGT,
                lhs.0.into_float_value(),
                rhs.0.into_float_value(),
                "ugt.float",
            ),
            (float_types!(), Lt) => self.builder.build_float_compare(
                FloatPredicate::ULT,
                lhs.0.into_float_value(),
                rhs.0.into_float_value(),
                "ult.float",
            ),
            (ty, op) => {
                return Err(format!(
                    "Unsupported type/op combination in `cmp`: `(ty:{} / op:{})`",
                    ty, op
                ))
            }
        };

        Ok(self
            .builder
            .build_int_cast(inst, self.context.bool_type(), "cmp.bool")
            .as_basic_value_enum())
    }

    pub(super) fn assign(&self, lhs: &Expression, rhs: BasicValueEnum<'ctx>) -> ExprResult<'ctx> {
        let lhs_name = match lhs {
            Expression::Ident { name, .. } => name,
            _ => unreachable!("Fatal: Bad LHS in codegen assignment: `{}`", lhs),
        };

        let lhs_var = self
            .symbol_table
            .get(lhs_name)
            .ok_or(format!("Unknown variable in assignment: {}", lhs_name))?
            .to_owned();

        self.builder.build_store(lhs_var, rhs);

        Ok(rhs)
    }

    // Unary operations

    pub(super) fn neg(&self, rhs: (BasicValueEnum<'ctx>, Type)) -> ExprResult<'ctx> {
        match rhs.1 {
            int_types!() => Ok(self
                .builder
                .build_int_neg(rhs.0.into_int_value(), "neg.int")
                .as_basic_value_enum()),
            float_types!() => Ok(self
                .builder
                .build_float_neg(rhs.0.into_float_value(), "neg.float")
                .as_basic_value_enum()),
            _ => Err("Unsupported type in `neg` operation".to_string()),
        }
    }
}
