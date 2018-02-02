/* Copyright 2017 Mozilla Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use std::io::Write;
use std::io::Result;

use wasmparser::ParserState;
use wasmparser::ExternalKind;
use wasmparser::Type;
use wasmparser::FuncType;
use wasmparser::TableType;
use wasmparser::MemoryType;
use wasmparser::GlobalType;
use wasmparser::ImportSectionEntryType;
use wasmparser::ResizableLimits;
use wasmparser::Operator;
use wasmparser::BrTable;
use wasmparser::MemoryImmediate;
use wasmparser::Ieee32;
use wasmparser::Ieee64;

macro_rules! format_to_vec {
    ($fmt:expr, $($arg:tt)+) => {{
        let mut name = Vec::new();
        let s = &format!($fmt, $($arg)+);
        name.extend_from_slice(s.as_bytes());
        name
    }};
}

fn get_func_name(index: u32, is_import: bool, _is_ref: bool) -> Vec<u8> {
    if is_import {
        format_to_vec!("$import{}", index)
    } else {
        format_to_vec!("$func{}", index)
    }
}

fn get_global_name(index: u32, _is_ref: bool) -> Vec<u8> {
    format_to_vec!("$global{}", index)
}

fn get_table_name(index: u32, _is_ref: bool) -> Vec<u8> {
    format_to_vec!("$table{}", index)
}

fn get_memory_name(index: u32, is_ref: bool) -> Vec<u8> {
    if is_ref {
        format_to_vec!("{}", index)
    } else {
        format_to_vec!("(;{};)", index)
    }
}

fn get_type_name(index: u32, _is_ref: bool) -> Vec<u8> {
    format_to_vec!("$type{}", index)
}

fn get_var_name(_func_index: u32, index: u32, _is_ref: bool) -> Vec<u8> {
    format_to_vec!("$var{}", index)
}

fn get_label(index: u32) -> Option<Vec<u8>> {
    Some(format_to_vec!("$label{}", index))
}

// Original can be found at
// https://github.com/stoklund/cretonne/blob/dc809628f4c/lib/cretonne/src/ir/immediates.rs#L299
//
// Format a floating point number in a way that is reasonably human-readable, and that can be
// converted back to binary without any rounding issues. The hexadecimal formatting of normal and
// subnormal numbers is compatible with C99 and the `printf "%a"` format specifier. The NaN and Inf
// formats are not supported by C99.
//
// The encoding parameters are:
//
// w - exponent field width in bits
// t - trailing significand field width in bits
//
fn format_float(bits: u64, w: u8, t: u8) -> Vec<u8> {
    debug_assert!(w > 0 && w <= 16, "Invalid exponent range");
    debug_assert!(1 + w + t <= 64, "Too large IEEE format for u64");
    debug_assert!((t + w + 1).is_power_of_two(), "Unexpected IEEE format size");

    let max_e_bits = (1u64 << w) - 1;
    let t_bits = bits & ((1u64 << t) - 1); // Trailing significand.
    let e_bits = (bits >> t) & max_e_bits; // Biased exponent.
    let sign_bit = (bits >> (w + t)) & 1;

    let bias: i32 = (1 << (w - 1)) - 1;
    let e = e_bits as i32 - bias; // Unbiased exponent.
    let emin = 1 - bias; // Minimum exponent.

    // How many hexadecimal digits are needed for the trailing significand?
    let digits = (t + 3) / 4;
    // Trailing significand left-aligned in `digits` hexadecimal digits.
    let left_t_bits = t_bits << (4 * digits - t);

    let mut result = Vec::new();
    // All formats share the leading sign.
    if sign_bit != 0 {
        result.push(b'-');
    }

    if e_bits == 0 {
        if t_bits == 0 {
            // Zero.
            result.extend_from_slice(b"0.0");
        } else {
            // Subnormal.
            result
                .extend_from_slice(format!("0x0.{0:01$x}p{2}", left_t_bits, digits as usize, emin)
                                       .as_bytes());
        }
    } else if e_bits == max_e_bits {
        if t_bits == 0 {
            // Infinity.
            result.extend_from_slice(b"inf");
        } else {
            // NaN.
            let default_payload = 1 << (t - 1);
            if t_bits != default_payload {
                result.extend_from_slice(format!("nan:0x{:x}", t_bits).as_bytes());
            } else {
                result.extend_from_slice(b"nan")
            }
        }
    } else {
        // Normal number.
        result.extend_from_slice(format!("0x1.{0:01$x}p{2}", left_t_bits, digits as usize, e)
                                     .as_bytes());
    }
    result
}

struct BackrefLabel {
    use_label: bool,
    label: Option<Vec<u8>>,
    buffer: Vec<u8>,
}

pub struct Writer<'a> {
    writable: &'a mut Write,
    types: Vec<FuncType>,
    func_types: Vec<u32>,
    func_index: usize,
    import_count: usize,
    global_count: usize,
    table_count: usize,
    memory_count: usize,
    indent: u32,
    label_index: usize,
    backref_labels: Vec<BackrefLabel>,
}

impl<'a> Writer<'a> {
    pub fn new(writable: &mut Write) -> Writer {
        Writer {
            writable,
            types: Vec::new(),
            func_types: Vec::new(),
            func_index: 0,
            import_count: 0,
            global_count: 0,
            table_count: 0,
            memory_count: 0,
            indent: 0,
            label_index: 0,
            backref_labels: Vec::new(),
        }
    }

    fn w(&mut self) -> &mut Write {
        if !self.backref_labels.is_empty() {
            return &mut self.backref_labels.last_mut().unwrap().buffer;
        }
        self.writable
    }

    fn write_bytes(&mut self, bytes: &[u8]) -> Result<()> {
        self.w().write_all(bytes)
    }

    fn write_string_chunk(&mut self, bytes: &[u8]) -> Result<()> {
        let mut i = 0;
        let mut j = 0;
        while i < bytes.len() {
            let byte = bytes[i];
            if byte < 0x20 || byte >= 0x7F || byte == b'\"' || byte == b'\\' {
                if j < i {
                    self.write_bytes(&bytes[j..i])?;
                }
                self.w().write_fmt(format_args!("\\{:02x}", byte))?;
                j = i + 1;
            }
            i += 1;
        }
        if j < bytes.len() {
            self.write_bytes(&bytes[j..])?;
        }
        Ok(())
    }

    fn write_string(&mut self, bytes: &[u8]) -> Result<()> {
        self.write_bytes(b"\"")?;
        self.write_string_chunk(bytes)?;
        self.write_bytes(b"\"")?;
        Ok(())
    }

    fn write_u32(&mut self, num: u32) -> Result<()> {
        self.w().write_fmt(format_args!("{}", num))
    }

    fn write_type(&mut self, ty: Type) -> Result<()> {
        match ty {
            Type::I32 => self.write_bytes(b"i32"),
            Type::I64 => self.write_bytes(b"i64"),
            Type::F32 => self.write_bytes(b"f32"),
            Type::F64 => self.write_bytes(b"f64"),
            Type::AnyFunc => self.write_bytes(b"anyfunc"),
            _ => panic!("Unexpected type"),
        }
    }

    fn write_func_type(&mut self, func_type: &FuncType) -> Result<()> {
        if let Type::Func = func_type.form {
            if func_type.params.len() > 0 {
                self.write_bytes(b" (param")?;
                for i in 0..func_type.params.len() {
                    self.write_bytes(b" ")?;
                    self.write_type(func_type.params[i])?;
                }
                self.write_bytes(b")")?;
            }
            if func_type.returns.len() > 0 {
                self.write_bytes(b" (result")?;
                for i in 0..func_type.returns.len() {
                    self.write_bytes(b" ")?;
                    self.write_type(func_type.returns[i])?;
                }
                self.write_bytes(b")")?;
            }
        } else {
            panic!("NYI other function form");
        }
        Ok(())
    }

    fn write_limits(&mut self, limits: &ResizableLimits) -> Result<()> {
        self.write_u32(limits.initial)?;
        if let Some(maximum) = limits.maximum {
            self.write_bytes(b" ")?;
            self.write_u32(maximum)?;
        }
        Ok(())
    }

    fn write_global_type(&mut self, global_type: &GlobalType) -> Result<()> {
        if !global_type.mutable {
            return self.write_type(global_type.content_type);
        }
        self.write_bytes(b"(mut ")?;
        self.write_type(global_type.content_type)?;
        self.write_bytes(b")")
    }

    fn write_br_table(&mut self, br_table: &BrTable) -> Result<()> {
        for index in br_table {
            self.write_bytes(b" ")?;
            self.use_label(index)?;
        }
        Ok(())
    }

    fn write_func_name_ref(&mut self, func_index: u32) -> Result<()> {
        let is_import = (func_index as usize) < self.import_count;
        self.write_bytes(&get_func_name(func_index, is_import, true))
    }

    fn write_local_name_ref(&mut self, local_index: u32) -> Result<()> {
        let func_index = self.func_index as u32;
        self.write_bytes(&get_var_name(func_index, local_index, true))
    }

    fn write_global_name_ref(&mut self, index: u32) -> Result<()> {
        self.write_bytes(&get_global_name(index, true))
    }

    fn write_i32(&mut self, value: i32) -> Result<()> {
        let s = format!("{}", value);
        self.write_bytes(s.as_bytes())
    }

    fn write_i64(&mut self, value: i64) -> Result<()> {
        let s = format!("{}", value);
        self.write_bytes(s.as_bytes())
    }

    fn write_f32(&mut self, value: &Ieee32) -> Result<()> {
        let bits = value.bits();
        self.write_bytes(&format_float(bits as u64, 8, 23))
    }

    fn write_f64(&mut self, value: &Ieee64) -> Result<()> {
        let bits = value.bits();
        self.write_bytes(&format_float(bits, 11, 52))
    }

    fn write_block_type(&mut self, block_type: Type) -> Result<()> {
        if let Type::EmptyBlockType = block_type {
            return Ok(());
        }
        self.write_bytes(b" (result ")?;
        self.write_type(block_type)?;
        self.write_bytes(b")")
    }

    fn write_memarg(&mut self, memarg: &MemoryImmediate, default_align_flags: u32) -> Result<()> {
        if memarg.offset != 0 {
            self.write_bytes(b" offset=")?;
            self.write_u32(memarg.offset)?;
        }
        if memarg.flags != default_align_flags {
            // hide default flags
            self.write_bytes(b" align=")?;
            self.write_u32(1 << memarg.flags)?;
        }
        Ok(())
    }

    fn start_label_block(&mut self) {
        let buffer = Vec::new();
        self.backref_labels
            .push(BackrefLabel {
                      use_label: false,
                      label: None,
                      buffer: buffer,
                  });
    }

    fn end_label_block(&mut self) -> Result<()> {
        let backref_label = self.backref_labels.pop().unwrap();
        if backref_label.label.is_none() {
            return self.write_bytes(&backref_label.buffer);
        }
        let label = backref_label.label.unwrap();
        self.write_bytes(b" ")?;
        self.write_bytes(&label)?;
        self.write_bytes(&backref_label.buffer)?;
        self.write_bytes(b" ")?;
        self.write_bytes(&label)
    }

    fn use_label(&mut self, depth: u32) -> Result<()> {
        if depth as usize >= self.backref_labels.len() {
            return self.write_u32(depth);
        }
        let index = self.backref_labels.len() - 1 - (depth as usize);
        {
            let ref mut backref_label = self.backref_labels[index];
            if !backref_label.use_label {
                backref_label.label = get_label(self.label_index as u32);
                self.label_index += 1;
                backref_label.use_label = true;
            }
        }

        if self.backref_labels[index].label.is_none() {
            self.write_u32(depth)
        } else {
            let label = self.backref_labels[index].label.as_ref().unwrap().clone();
            self.write_bytes(&label)
        }
    }

    fn write_operator(&mut self, operator: &Operator) -> Result<()> {
        match *operator {
            Operator::Unreachable => self.write_bytes(b"unreachable"),
            Operator::Nop => self.write_bytes(b"nop"),
            Operator::Block { ty } => {
                self.write_bytes(b"block")?;
                self.start_label_block();
                self.write_block_type(ty)
            }
            Operator::Loop { ty } => {
                self.write_bytes(b"loop")?;
                self.start_label_block();
                self.write_block_type(ty)
            }
            Operator::If { ty } => {
                self.write_bytes(b"if")?;
                self.start_label_block();
                self.write_block_type(ty)
            }
            Operator::Else => self.write_bytes(b"else"),
            Operator::End => {
                self.write_bytes(b"end")?;
                self.end_label_block()
            }
            Operator::Br { relative_depth } => {
                self.write_bytes(b"br ")?;
                self.use_label(relative_depth)
            }
            Operator::BrIf { relative_depth } => {
                self.write_bytes(b"br_if ")?;
                self.use_label(relative_depth)
            }
            Operator::BrTable { ref table } => {
                self.write_bytes(b"br_table")?;
                self.write_br_table(table)
            }
            Operator::Return => self.write_bytes(b"return"),
            Operator::Call { function_index } => {
                self.write_bytes(b"call ")?;
                self.write_func_name_ref(function_index)
            }
            Operator::CallIndirect { index, .. } => {
                self.write_bytes(b"call_indirect ")?;
                self.write_bytes(&get_type_name(index, true))
            }
            Operator::Drop => self.write_bytes(b"drop"),
            Operator::Select => self.write_bytes(b"select"),
            Operator::GetLocal { local_index } => {
                self.write_bytes(b"get_local ")?;
                self.write_local_name_ref(local_index)
            }
            Operator::SetLocal { local_index } => {
                self.write_bytes(b"set_local ")?;
                self.write_local_name_ref(local_index)
            }
            Operator::TeeLocal { local_index } => {
                self.write_bytes(b"tee_local ")?;
                self.write_local_name_ref(local_index)
            }
            Operator::GetGlobal { global_index } => {
                self.write_bytes(b"get_global ")?;
                self.write_global_name_ref(global_index)
            }
            Operator::SetGlobal { global_index } => {
                self.write_bytes(b"set_global ")?;
                self.write_global_name_ref(global_index)
            }
            Operator::I32Load { ref memarg } => {
                self.write_bytes(b"i32.load")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64Load { ref memarg } => {
                self.write_bytes(b"i64.load")?;
                self.write_memarg(memarg, 3)
            }
            Operator::F32Load { ref memarg } => {
                self.write_bytes(b"f32.load")?;
                self.write_memarg(memarg, 2)
            }
            Operator::F64Load { ref memarg } => {
                self.write_bytes(b"f64.load")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32Load8S { ref memarg } => {
                self.write_bytes(b"i32.load8_s")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32Load8U { ref memarg } => {
                self.write_bytes(b"i32.load8_u")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32Load16S { ref memarg } => {
                self.write_bytes(b"i32.load16_s")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I32Load16U { ref memarg } => {
                self.write_bytes(b"i32.load16_u")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64Load8S { ref memarg } => {
                self.write_bytes(b"i64.load8_s")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64Load8U { ref memarg } => {
                self.write_bytes(b"i64.load8_u")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64Load16S { ref memarg } => {
                self.write_bytes(b"i64.load16_s")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64Load16U { ref memarg } => {
                self.write_bytes(b"i64.load16_u")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64Load32S { ref memarg } => {
                self.write_bytes(b"i64.load32_s")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64Load32U { ref memarg } => {
                self.write_bytes(b"i64.load32_u")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32Store { ref memarg } => {
                self.write_bytes(b"i32.store")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64Store { ref memarg } => {
                self.write_bytes(b"i64.store")?;
                self.write_memarg(memarg, 3)
            }
            Operator::F32Store { ref memarg } => {
                self.write_bytes(b"f32.store")?;
                self.write_memarg(memarg, 2)
            }
            Operator::F64Store { ref memarg } => {
                self.write_bytes(b"f64.store")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32Store8 { ref memarg } => {
                self.write_bytes(b"i32.store8")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32Store16 { ref memarg } => {
                self.write_bytes(b"i32.store16")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64Store8 { ref memarg } => {
                self.write_bytes(b"i64.store8")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64Store16 { ref memarg } => {
                self.write_bytes(b"i64.store16")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64Store32 { ref memarg } => {
                self.write_bytes(b"i64.store32")?;
                self.write_memarg(memarg, 2)
            }
            Operator::CurrentMemory { .. } => self.write_bytes(b"current_memory"),
            Operator::GrowMemory { .. } => self.write_bytes(b"grow_memory"),
            Operator::I32Const { value } => {
                self.write_bytes(b"i32.const ")?;
                self.write_i32(value)
            }
            Operator::I64Const { value } => {
                self.write_bytes(b"i64.const ")?;
                self.write_i64(value)
            }
            Operator::F32Const { ref value } => {
                self.write_bytes(b"f32.const ")?;
                self.write_f32(value)
            }
            Operator::F64Const { ref value } => {
                self.write_bytes(b"f64.const ")?;
                self.write_f64(value)
            }
            Operator::I32Eqz => self.write_bytes(b"i32.eqz"),
            Operator::I32Eq => self.write_bytes(b"i32.eq"),
            Operator::I32Ne => self.write_bytes(b"i32.ne"),
            Operator::I32LtS => self.write_bytes(b"i32.lt_s"),
            Operator::I32LtU => self.write_bytes(b"i32.lt_u"),
            Operator::I32GtS => self.write_bytes(b"i32.gt_s"),
            Operator::I32GtU => self.write_bytes(b"i32.gt_u"),
            Operator::I32LeS => self.write_bytes(b"i32.le_s"),
            Operator::I32LeU => self.write_bytes(b"i32.le_u"),
            Operator::I32GeS => self.write_bytes(b"i32.ge_s"),
            Operator::I32GeU => self.write_bytes(b"i32.ge_u"),
            Operator::I64Eqz => self.write_bytes(b"i64.eqz"),
            Operator::I64Eq => self.write_bytes(b"i64.eq"),
            Operator::I64Ne => self.write_bytes(b"i64.ne"),
            Operator::I64LtS => self.write_bytes(b"i64.lt_s"),
            Operator::I64LtU => self.write_bytes(b"i64.lt_u"),
            Operator::I64GtS => self.write_bytes(b"i64.gt_s"),
            Operator::I64GtU => self.write_bytes(b"i64.gt_u"),
            Operator::I64LeS => self.write_bytes(b"i64.le_s"),
            Operator::I64LeU => self.write_bytes(b"i64.le_u"),
            Operator::I64GeS => self.write_bytes(b"i64.ge_s"),
            Operator::I64GeU => self.write_bytes(b"i64.ge_u"),
            Operator::F32Eq => self.write_bytes(b"f32.eq"),
            Operator::F32Ne => self.write_bytes(b"f32.ne"),
            Operator::F32Lt => self.write_bytes(b"f32.lt"),
            Operator::F32Gt => self.write_bytes(b"f32.gt"),
            Operator::F32Le => self.write_bytes(b"f32.le"),
            Operator::F32Ge => self.write_bytes(b"f32.ge"),
            Operator::F64Eq => self.write_bytes(b"f64.eq"),
            Operator::F64Ne => self.write_bytes(b"f64.ne"),
            Operator::F64Lt => self.write_bytes(b"f64.lt"),
            Operator::F64Gt => self.write_bytes(b"f64.gt"),
            Operator::F64Le => self.write_bytes(b"f64.le"),
            Operator::F64Ge => self.write_bytes(b"f64.ge"),
            Operator::I32Clz => self.write_bytes(b"i32.clz"),
            Operator::I32Ctz => self.write_bytes(b"i32.ctz"),
            Operator::I32Popcnt => self.write_bytes(b"i32.popcnt"),
            Operator::I32Add => self.write_bytes(b"i32.add"),
            Operator::I32Sub => self.write_bytes(b"i32.sub"),
            Operator::I32Mul => self.write_bytes(b"i32.mul"),
            Operator::I32DivS => self.write_bytes(b"i32.div_s"),
            Operator::I32DivU => self.write_bytes(b"i32.div_u"),
            Operator::I32RemS => self.write_bytes(b"i32.rem_s"),
            Operator::I32RemU => self.write_bytes(b"i32.rem_u"),
            Operator::I32And => self.write_bytes(b"i32.and"),
            Operator::I32Or => self.write_bytes(b"i32.or"),
            Operator::I32Xor => self.write_bytes(b"i32.xor"),
            Operator::I32Shl => self.write_bytes(b"i32.shl"),
            Operator::I32ShrS => self.write_bytes(b"i32.shr_s"),
            Operator::I32ShrU => self.write_bytes(b"i32.shr_u"),
            Operator::I32Rotl => self.write_bytes(b"i32.rotl"),
            Operator::I32Rotr => self.write_bytes(b"i32.rotr"),
            Operator::I64Clz => self.write_bytes(b"i64.clz"),
            Operator::I64Ctz => self.write_bytes(b"i64.ctz"),
            Operator::I64Popcnt => self.write_bytes(b"i64.popcnt"),
            Operator::I64Add => self.write_bytes(b"i64.add"),
            Operator::I64Sub => self.write_bytes(b"i64.sub"),
            Operator::I64Mul => self.write_bytes(b"i64.mul"),
            Operator::I64DivS => self.write_bytes(b"i64.div_s"),
            Operator::I64DivU => self.write_bytes(b"i64.div_u"),
            Operator::I64RemS => self.write_bytes(b"i64.rem_s"),
            Operator::I64RemU => self.write_bytes(b"i64.rem_u"),
            Operator::I64And => self.write_bytes(b"i64.and"),
            Operator::I64Or => self.write_bytes(b"i64.or"),
            Operator::I64Xor => self.write_bytes(b"i64.xor"),
            Operator::I64Shl => self.write_bytes(b"i64.shl"),
            Operator::I64ShrS => self.write_bytes(b"i64.shr_s"),
            Operator::I64ShrU => self.write_bytes(b"i64.shr_u"),
            Operator::I64Rotl => self.write_bytes(b"i64.rotl"),
            Operator::I64Rotr => self.write_bytes(b"i64.rotr"),
            Operator::F32Abs => self.write_bytes(b"f32.abs"),
            Operator::F32Neg => self.write_bytes(b"f32.neg"),
            Operator::F32Ceil => self.write_bytes(b"f32.ceil"),
            Operator::F32Floor => self.write_bytes(b"f32.floor"),
            Operator::F32Trunc => self.write_bytes(b"f32.trunc"),
            Operator::F32Nearest => self.write_bytes(b"f32.nearest"),
            Operator::F32Sqrt => self.write_bytes(b"f32.sqrt"),
            Operator::F32Add => self.write_bytes(b"f32.add"),
            Operator::F32Sub => self.write_bytes(b"f32.sub"),
            Operator::F32Mul => self.write_bytes(b"f32.mul"),
            Operator::F32Div => self.write_bytes(b"f32.div"),
            Operator::F32Min => self.write_bytes(b"f32.min"),
            Operator::F32Max => self.write_bytes(b"f32.max"),
            Operator::F32Copysign => self.write_bytes(b"f32.copysign"),
            Operator::F64Abs => self.write_bytes(b"f64.abs"),
            Operator::F64Neg => self.write_bytes(b"f64.neg"),
            Operator::F64Ceil => self.write_bytes(b"f64.ceil"),
            Operator::F64Floor => self.write_bytes(b"f64.floor"),
            Operator::F64Trunc => self.write_bytes(b"f64.trunc"),
            Operator::F64Nearest => self.write_bytes(b"f64.nearest"),
            Operator::F64Sqrt => self.write_bytes(b"f64.sqrt"),
            Operator::F64Add => self.write_bytes(b"f64.add"),
            Operator::F64Sub => self.write_bytes(b"f64.sub"),
            Operator::F64Mul => self.write_bytes(b"f64.mul"),
            Operator::F64Div => self.write_bytes(b"f64.div"),
            Operator::F64Min => self.write_bytes(b"f64.min"),
            Operator::F64Max => self.write_bytes(b"f64.max"),
            Operator::F64Copysign => self.write_bytes(b"f64.copysign"),
            Operator::I32WrapI64 => self.write_bytes(b"i32.wrap/i64"),
            Operator::I32TruncSF32 => self.write_bytes(b"i32.trunc_s/f32"),
            Operator::I32TruncUF32 => self.write_bytes(b"i32.trunc_u/f32"),
            Operator::I32TruncSF64 => self.write_bytes(b"i32.trunc_s/f64"),
            Operator::I32TruncUF64 => self.write_bytes(b"i32.trunc_u/f64"),
            Operator::I64ExtendSI32 => self.write_bytes(b"i64.extend_s/i32"),
            Operator::I64ExtendUI32 => self.write_bytes(b"i64.extend_u/i32"),
            Operator::I64TruncSF32 => self.write_bytes(b"i64.trunc_s/f32"),
            Operator::I64TruncUF32 => self.write_bytes(b"i64.trunc_u/f32"),
            Operator::I64TruncSF64 => self.write_bytes(b"i64.trunc_s/f64"),
            Operator::I64TruncUF64 => self.write_bytes(b"i64.trunc_u/f64"),
            Operator::F32ConvertSI32 => self.write_bytes(b"f32.convert_s/i32"),
            Operator::F32ConvertUI32 => self.write_bytes(b"f32.convert_u/i32"),
            Operator::F32ConvertSI64 => self.write_bytes(b"f32.convert_s/i64"),
            Operator::F32ConvertUI64 => self.write_bytes(b"f32.convert_u/i64"),
            Operator::F32DemoteF64 => self.write_bytes(b"f32.demote/f64"),
            Operator::F64ConvertSI32 => self.write_bytes(b"f64.convert_s/i32"),
            Operator::F64ConvertUI32 => self.write_bytes(b"f64.convert_u/i32"),
            Operator::F64ConvertSI64 => self.write_bytes(b"f64.convert_s/i64"),
            Operator::F64ConvertUI64 => self.write_bytes(b"f64.convert_u/i64"),
            Operator::F64PromoteF32 => self.write_bytes(b"f64.promote/f32"),
            Operator::I32ReinterpretF32 => self.write_bytes(b"i32.reinterpret/f32"),
            Operator::I64ReinterpretF64 => self.write_bytes(b"i64.reinterpret/f64"),
            Operator::F32ReinterpretI32 => self.write_bytes(b"f32.reinterpret/i32"),
            Operator::F64ReinterpretI64 => self.write_bytes(b"f64.reinterpret/i64"),
            Operator::I32TruncSSatF32 => self.write_bytes(b"i32.trunc_s:sat/f32"),
            Operator::I32TruncUSatF32 => self.write_bytes(b"i32.trunc_u:sat/f32"),
            Operator::I32TruncSSatF64 => self.write_bytes(b"i32.trunc_s:sat/f64"),
            Operator::I32TruncUSatF64 => self.write_bytes(b"i32.trunc_u:sat/f64"),
            Operator::I64TruncSSatF32 => self.write_bytes(b"i64.trunc_s:sat/f32"),
            Operator::I64TruncUSatF32 => self.write_bytes(b"i64.trunc_u:sat/f32"),
            Operator::I64TruncSSatF64 => self.write_bytes(b"i64.trunc_s:sat/f64"),
            Operator::I64TruncUSatF64 => self.write_bytes(b"i64.trunc_u:sat/f64"),
            Operator::I32Extend8S => self.write_bytes(b"i32.extend8_s"),
            Operator::I32Extend16S => self.write_bytes(b"i32.extend16_s"),
            Operator::I64Extend8S => self.write_bytes(b"i64.extend8_s"),
            Operator::I64Extend16S => self.write_bytes(b"i64.extend16_s"),
            Operator::I64Extend32S => self.write_bytes(b"i64.extend32_s"),
            Operator::Wake { ref memarg } => {
                self.write_bytes(b"atomic.wake")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32Wait { ref memarg } => {
                self.write_bytes(b"i32.atomic.wait")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64Wait { ref memarg } => {
                self.write_bytes(b"i64.atomic.wait")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicLoad { ref memarg } => {
                self.write_bytes(b"i32.atomic.load")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64AtomicLoad { ref memarg } => {
                self.write_bytes(b"i64.atomic.load")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicLoad8U { ref memarg } => {
                self.write_bytes(b"i32.atomic.load8_u")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32AtomicLoad16U { ref memarg } => {
                self.write_bytes(b"i32.atomic.load16_u")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicLoad8U { ref memarg } => {
                self.write_bytes(b"i64.atomic.load8_u")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64AtomicLoad16U { ref memarg } => {
                self.write_bytes(b"i64.atomic.load16_u")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicLoad32U { ref memarg } => {
                self.write_bytes(b"i64.atomic.load32_u")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32AtomicStore { ref memarg } => {
                self.write_bytes(b"i32.atomic.store")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64AtomicStore { ref memarg } => {
                self.write_bytes(b"i64.atomic.store")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicStore8 { ref memarg } => {
                self.write_bytes(b"i32.atomic.store8")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32AtomicStore16 { ref memarg } => {
                self.write_bytes(b"i32.atomic.store16")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicStore8 { ref memarg } => {
                self.write_bytes(b"i64.atomic.store8")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64AtomicStore16 { ref memarg } => {
                self.write_bytes(b"i64.atomic.store16")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicStore32 { ref memarg } => {
                self.write_bytes(b"i64.atomic.store32")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32AtomicRmwAdd { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw.add")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64AtomicRmwAdd { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw.add")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicRmw8UAdd { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw8_u.add")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32AtomicRmw16UAdd { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw16_u.add")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw8UAdd { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw8_u.add")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64AtomicRmw16UAdd { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw16_u.add")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw32UAdd { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw32_u.add")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32AtomicRmwSub { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw.sub")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64AtomicRmwSub { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw.sub")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicRmw8USub { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw8_u.sub")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32AtomicRmw16USub { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw16_u.sub")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw8USub { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw8_u.sub")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64AtomicRmw16USub { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw16_u.sub")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw32USub { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw32_u.sub")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32AtomicRmwAnd { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw.and")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64AtomicRmwAnd { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw.and")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicRmw8UAnd { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw8_u.and")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32AtomicRmw16UAnd { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw16_u.and")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw8UAnd { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw8_u.and")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64AtomicRmw16UAnd { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw16_u.and")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw32UAnd { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw32_u.and")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32AtomicRmwOr { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw.or")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64AtomicRmwOr { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw.or")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicRmw8UOr { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw8_u.or")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32AtomicRmw16UOr { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw16_u.or")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw8UOr { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw8_u.or")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64AtomicRmw16UOr { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw16_u.or")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw32UOr { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw32_u.or")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32AtomicRmwXor { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw.xor")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64AtomicRmwXor { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw.xor")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicRmw8UXor { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw8_u.xor")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32AtomicRmw16UXor { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw16_u.xor")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw8UXor { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw8_u.xor")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64AtomicRmw16UXor { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw16_u.xor")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw32UXor { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw32_u.xor")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32AtomicRmwXchg { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw.xchg")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64AtomicRmwXchg { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw.xchg")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicRmw8UXchg { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw8_u.xchg")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32AtomicRmw16UXchg { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw16_u.xchg")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw8UXchg { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw8_u.xchg")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64AtomicRmw16UXchg { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw16_u.xchg")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw32UXchg { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw32_u.xchg")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I32AtomicRmwCmpxchg { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw.cmpxchg")?;
                self.write_memarg(memarg, 2)
            }
            Operator::I64AtomicRmwCmpxchg { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw.cmpxchg")?;
                self.write_memarg(memarg, 3)
            }
            Operator::I32AtomicRmw8UCmpxchg { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw8_u.cmpxchg")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I32AtomicRmw16UCmpxchg { ref memarg } => {
                self.write_bytes(b"i32.atomic.rmw16_u.cmpxchg")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw8UCmpxchg { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw8_u.cmpxchg")?;
                self.write_memarg(memarg, 0)
            }
            Operator::I64AtomicRmw16UCmpxchg { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw16_u.cmpxchg")?;
                self.write_memarg(memarg, 1)
            }
            Operator::I64AtomicRmw32UCmpxchg { ref memarg } => {
                self.write_bytes(b"i64.atomic.rmw32_u.cmpxchg")?;
                self.write_memarg(memarg, 2)
            }
        }
    }

    fn write_import_source(&mut self, module: &[u8], field: &[u8]) -> Result<()> {
        self.write_string(module)?;
        self.write_bytes(b" ")?;
        self.write_string(field)
    }

    pub fn write(&mut self, state: &ParserState) -> Result<()> {
        match *state {
            ParserState::EndWasm => {
                self.write_bytes(b")\n")?;
            }
            ParserState::Error(_) => unreachable!(),
            ParserState::BeginWasm { .. } => {
                self.write_bytes(b"(module\n")?;
            }
            ParserState::EndSection => {}
            ParserState::BeginSection { .. } => {}
            ParserState::ExportSectionEntry {
                field,
                ref kind,
                index,
            } => {
                self.write_bytes(b"  (export ")?;
                self.write_string(field)?;
                self.write_bytes(b" ")?;
                match *kind {
                    ExternalKind::Function => {
                        self.write_bytes(b"(func ")?;
                        self.write_func_name_ref(index)?;
                        self.write_bytes(b")")?;
                    }
                    ExternalKind::Table => {
                        self.write_bytes(b"(table ")?;
                        self.write_bytes(&get_table_name(index, true))?;
                        self.write_bytes(b")")?;
                    }
                    ExternalKind::Memory => {
                        self.write_bytes(b"(memory ")?;
                        self.write_bytes(&get_memory_name(index, true))?;
                        self.write_bytes(b")")?;
                    }
                    ExternalKind::Global => {
                        self.write_bytes(b"(global ")?;
                        self.write_bytes(&get_global_name(index, true))?;
                        self.write_bytes(b")")?;
                    }
                }
                self.write_bytes(b")\n")?;
            }
            ParserState::ImportSectionEntry {
                module,
                field,
                ref ty,
                ..
            } => {
                self.write_bytes(b"  (import ")?;
                self.write_import_source(module, field)?;
                match *ty {
                    ImportSectionEntryType::Function(type_index) => {
                        self.func_types.push(type_index);
                        let index = self.func_index as u32;
                        self.func_index += 1;
                        self.import_count += 1;
                        self.write_bytes(b" (func ")?;
                        self.write_bytes(&get_func_name(index, true, false))?;
                        let ty = self.types[type_index as usize].clone();
                        self.write_func_type(&ty)?;
                        self.write_bytes(b")")?;
                    }
                    ImportSectionEntryType::Table(ref table_type) => {
                        self.write_bytes(b" (table ")?;
                        let index = self.table_count as u32;
                        self.table_count += 1;
                        self.write_bytes(&get_table_name(index, false))?;
                        self.write_bytes(b" ")?;
                        self.write_limits(&table_type.limits)?;
                        self.write_bytes(b" ")?;
                        self.write_type(table_type.element_type)?;
                        self.write_bytes(b")")?;
                    }
                    ImportSectionEntryType::Memory(ref memory_type) => {
                        let index = self.memory_count as u32;
                        self.memory_count += 1;
                        self.write_bytes(b" (memory ")?;
                        self.write_bytes(&get_memory_name(index, false))?;
                        self.write_bytes(b" ")?;
                        self.write_limits(&memory_type.limits)?;
                        self.write_bytes(b")")?;
                    }
                    ImportSectionEntryType::Global(ref global_type) => {
                        let index = self.global_count as u32;
                        self.global_count += 1;
                        self.write_bytes(b" (global ")?;
                        self.write_bytes(&get_global_name(index, false))?;
                        self.write_bytes(b" ")?;
                        self.write_global_type(global_type)?;
                        self.write_bytes(b")")?;
                    }
                }
                self.write_bytes(b")\n")?;
            }
            ParserState::TypeSectionEntry(ref ty) => {
                self.write_bytes(b"  (type ")?;
                let index = self.types.len() as u32;
                self.types.push(ty.clone());
                self.write_bytes(&get_type_name(index, false))?;
                self.write_bytes(b" (func")?;
                self.write_func_type(ty)?;
                self.write_bytes(b"))\n")?;
            }
            ParserState::TableSectionEntry(TableType {
                                               element_type,
                                               ref limits,
                                           }) => {
                let index = self.table_count as u32;
                self.table_count += 1;
                self.write_bytes(b"  (table ")?;
                self.write_bytes(&get_table_name(index, false))?;
                self.write_bytes(b" ")?;
                self.write_limits(limits)?;
                self.write_bytes(b" ")?;
                self.write_type(element_type)?;
                self.write_bytes(b")\n")?;

            }
            ParserState::MemorySectionEntry(MemoryType { ref limits, shared }) => {
                let index = self.memory_count as u32;
                self.memory_count += 1;
                self.write_bytes(b"  (memory ")?;
                self.write_bytes(&get_memory_name(index, false))?;
                self.write_bytes(b" ")?;
                self.write_limits(limits)?;
                if shared {
                    self.write_bytes(b" shared")?;
                }
                self.write_bytes(b")\n")?;
            }
            ParserState::FunctionSectionEntry(index) => {
                self.func_types.push(index);
            }
            ParserState::BeginGlobalSectionEntry(ref global_type) => {
                self.write_bytes(b"  (global ")?;
                let index = self.global_count as u32;
                self.global_count += 1;
                self.write_bytes(&get_global_name(index, false))?;
                self.write_bytes(b" ")?;
                self.write_global_type(global_type)?;
            }
            ParserState::EndGlobalSectionEntry => {
                self.write_bytes(b")\n")?;
            }
            ParserState::BeginFunctionBody { .. } => {
                self.write_bytes(b"  (func ")?;
                let is_import = self.func_index < self.import_count;
                let index = self.func_index as u32;
                self.write_bytes(&get_func_name(index, is_import, false))?;
                let func_type_index = self.func_types[self.func_index] as usize;
                let func_type: FuncType = self.types[func_type_index].clone();
                for i in 0..func_type.params.len() {
                    self.write_bytes(b" (param ")?;
                    self.write_bytes(&get_var_name(index, i as u32, false))?;
                    self.write_bytes(b" ")?;
                    self.write_type(func_type.params[i])?;
                    self.write_bytes(b")")?;
                }
                for i in 0..func_type.returns.len() {
                    self.write_bytes(b" (result ")?;
                    self.write_type(func_type.returns[i])?;
                    self.write_bytes(b")")?;
                }
                self.write_bytes(b"\n")?;
                self.indent = 0;
                self.label_index = 0;
            }
            ParserState::FunctionBodyLocals { ref locals } => {
                if locals.len() > 0 {
                    self.write_bytes(b"   ")?;
                    let index = self.func_index as u32;
                    let func_type_index = self.func_types[self.func_index] as usize;
                    let func_type: FuncType = self.types[func_type_index].clone();
                    let mut local_index = func_type.params.len();
                    for &(j, ty) in locals {
                        for _ in 0..j {
                            self.write_bytes(b" (local ")?;
                            self.write_bytes(&get_var_name(index, local_index as u32, false))?;
                            self.write_bytes(b" ")?;
                            self.write_type(ty)?;
                            self.write_bytes(b")")?;
                            local_index += 1;
                        }
                    }
                    self.write_bytes(b"\n")?;
                }
            }
            ParserState::EndFunctionBody => {
                self.write_bytes(b"  )\n")?;
                self.func_index += 1;
            }
            ParserState::CodeOperator(ref operator) => {
                if let Operator::End = *operator {
                    if self.indent == 0 {
                        // Ignoring function's last end operator.
                        return Ok(());
                    }
                    self.indent -= 1;
                }
                self.write_bytes(b"    ")?;
                let mut indent = self.indent;
                if let Operator::Else = *operator {
                    indent -= 1;
                }
                for _ in 0..indent {
                    self.write_bytes(b"  ")?;
                }
                self.write_operator(operator)?;
                match *operator {
                    Operator::Block { .. } |
                    Operator::Loop { .. } |
                    Operator::If { .. } => self.indent += 1,
                    _ => {}
                }
                self.write_bytes(b"\n")?;
            }
            ParserState::BeginDataSectionEntry(_) => {
                self.write_bytes(b"  (data")?;
            }
            ParserState::BeginDataSectionEntryBody(_) => {
                self.write_bytes(b"\n    \"")?;
            }
            ParserState::DataSectionEntryBodyChunk(data) => {
                self.write_string_chunk(data)?;
            }
            ParserState::EndDataSectionEntryBody => {
                self.write_bytes(b"\"")?;
            }
            ParserState::EndDataSectionEntry => {
                self.write_bytes(b"\n  )\n")?;
            }
            ParserState::BeginInitExpressionBody |
            ParserState::EndInitExpressionBody => {}
            ParserState::InitExpressionOperator(ref operator) => {
                self.write_bytes(b" (")?;
                self.write_operator(operator)?;
                self.write_bytes(b")")?;
            }
            ParserState::StartSectionEntry(index) => {
                self.write_bytes(b"  (start ")?;
                self.write_func_name_ref(index)?;
                self.write_bytes(b")\n")?;
            }
            ParserState::BeginElementSectionEntry(_) => {
                self.write_bytes(b"  (elem")?;
            }
            ParserState::EndElementSectionEntry => {
                self.write_bytes(b")\n")?;
            }
            ParserState::ElementSectionEntryBody(ref elements) => {
                for index in elements.clone() {
                    self.write_bytes(b" ")?;
                    self.write_func_name_ref(index)?;
                }
            }
            ParserState::NameSectionEntry(_) |
            ParserState::RelocSectionHeader(_) |
            ParserState::RelocSectionEntry(_) |
            ParserState::SourceMappingURL(_) |
            ParserState::SectionRawData(_) |
            ParserState::LinkingSectionEntry(_) => {}
            _ => unreachable!(),
        }
        Ok(())
    }
}
