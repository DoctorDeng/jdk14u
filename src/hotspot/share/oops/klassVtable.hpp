/*
 * Copyright (c) 1997, 2019, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#ifndef SHARE_OOPS_KLASSVTABLE_HPP
#define SHARE_OOPS_KLASSVTABLE_HPP

#include "oops/oopsHierarchy.hpp"
#include "runtime/handles.hpp"
#include "utilities/growableArray.hpp"

// A klassVtable abstracts the variable-length vtable that is embedded in InstanceKlass
// and ArrayKlass.  klassVtable objects are used just as convenient transient accessors to the vtable,
// not to actually hold the vtable data.
// Note: the klassVtable should not be accessed before the class has been verified
// (until that point, the vtable is uninitialized).

// Currently a klassVtable contains a direct reference to the vtable data, and is therefore
// not preserved across GCs.
// 一个 klassVtable 抽象了嵌入在 InstanceKlass 和 ArrayKlass 中的可变长度 vtable.
// klassVtable 对象被用作 vtable 的便捷临时访问器，不实际保存 vtable 数据。
// 注意：在类被验证之前不应该访问 klassVtable (在那之前，vtable 是未初始化的).
//目前一个 klassVtable 包含对 vtable 数据的直接引用，因此不跨 GC 保留.
class vtableEntry;

class klassVtable {
  // vtable 对应的 klass 类型.
  Klass*       _klass;            // my klass
  // klass中 vtable 数据的起始偏移量.
  int          _tableOffset;      // offset of start of vtable data within klass
  // vtable 长度.
  int          _length;           // length of vtable (number of entries)
#ifndef PRODUCT
  int          _verify_count;     // to make verify faster
#endif

 public:
  klassVtable(Klass* klass, void* base, int length) : _klass(klass) {
    _tableOffset = (address)base - (address)klass; _length = length;
  }

  // accessors
  vtableEntry* table() const      { return (vtableEntry*)(address(_klass) + _tableOffset); }
  Klass* klass() const            { return _klass;  }
  int length() const              { return _length; }
  inline Method* method_at(int i) const;
  inline Method* unchecked_method_at(int i) const;

  // searching; all methods return -1 if not found
  int index_of_miranda(Symbol* name, Symbol* signature);

  void initialize_vtable(bool checkconstraints, TRAPS);   // initialize vtable of a new klass

  // computes vtable length (in words) and the number of miranda methods
  static void compute_vtable_size_and_num_mirandas(int* vtable_length,
                                                   int* num_new_mirandas,
                                                   GrowableArray<Method*>* all_mirandas,
                                                   const Klass* super,
                                                   Array<Method*>* methods,
                                                   AccessFlags class_flags,
                                                   u2 major_version,
                                                   Handle classloader,
                                                   Symbol* classname,
                                                   Array<InstanceKlass*>* local_interfaces,
                                                   TRAPS);

#if INCLUDE_JVMTI
  // RedefineClasses() API support:
  // If any entry of this vtable points to any of old_methods,
  // replace it with the corresponding new_method.
  // trace_name_printed is set to true if the current call has
  // printed the klass name so that other routines in the adjust_*
  // group don't print the klass name.
  bool adjust_default_method(int vtable_index, Method* old_method, Method* new_method);
  void adjust_method_entries(bool* trace_name_printed);
  bool check_no_old_or_obsolete_entries();
  void dump_vtable();
#endif // INCLUDE_JVMTI

  // Debugging code
  void print()                                              PRODUCT_RETURN;
  void verify(outputStream* st, bool force = false);
  static void print_statistics()                            PRODUCT_RETURN;

 protected:
  friend class vtableEntry;

 public:
  // Transitive overridng rules for class files < JDK1_7 use the older JVMS rules.
  // Overriding is determined as we create the vtable, so we use the class file version
  // of the class whose vtable we are calculating.
  enum { VTABLE_TRANSITIVE_OVERRIDE_VERSION = 51 } ;

 private:
  void copy_vtable_to(vtableEntry* start);
  int  initialize_from_super(Klass* super);
  void put_method_at(Method* m, int index);
  static bool needs_new_vtable_entry(const methodHandle& m,
                                     const Klass* super,
                                     Handle classloader,
                                     Symbol* classname,
                                     AccessFlags access_flags,
                                     u2 major_version,
                                     TRAPS);

  bool update_inherited_vtable(InstanceKlass* klass, const methodHandle& target_method, int super_vtable_len, int default_index, bool checkconstraints, TRAPS);
 InstanceKlass* find_transitive_override(InstanceKlass* initialsuper, const methodHandle& target_method, int vtable_index,
                                         Handle target_loader, Symbol* target_classname, Thread* THREAD);

  // support for miranda methods
  bool is_miranda_entry_at(int i);
  int fill_in_mirandas(int initialized, TRAPS);
  static bool is_miranda(Method* m, Array<Method*>* class_methods,
                         Array<Method*>* default_methods, const Klass* super,
                         bool is_interface);
  static void add_new_mirandas_to_lists(
      GrowableArray<Method*>* new_mirandas,
      GrowableArray<Method*>* all_mirandas,
      Array<Method*>* current_interface_methods,
      Array<Method*>* class_methods,
      Array<Method*>* default_methods,
      const Klass* super,
      bool is_interface);
  static void get_mirandas(
      GrowableArray<Method*>* new_mirandas,
      GrowableArray<Method*>* all_mirandas,
      const Klass* super,
      Array<Method*>* class_methods,
      Array<Method*>* default_methods,
      Array<InstanceKlass*>* local_interfaces,
      bool is_interface);
  void verify_against(outputStream* st, klassVtable* vt, int index);
  inline InstanceKlass* ik() const;
  // When loading a class from CDS archive at run time, and no class redefintion
  // has happened, it is expected that the class's itable/vtables are
  // laid out exactly the same way as they had been during dump time.
  // Therefore, in klassVtable::initialize_[iv]table, we do not layout the
  // tables again. Instead, we only rerun the process to create/check
  // the class loader constraints. In non-product builds, we add asserts to
  // guarantee that the table's layout would be the same as at dump time.
  //
  // If JVMTI redefines any class, the read-only shared memory are remapped
  // as read-write. A shared class' vtable/itable are re-initialized and
  // might have different layout due to class redefinition of the shared class
  // or its super types.
  bool is_preinitialized_vtable();
};


 
class vtableEntry {
  friend class VMStructs;
  friend class JVMCIVMStructs;

 public:
  // size in words
  static int size()          { return sizeof(vtableEntry) / wordSize; }
  static int size_in_bytes() { return sizeof(vtableEntry); }

  static int method_offset_in_bytes() { return offset_of(vtableEntry, _method); }
  Method* method() const    { return _method; }
  Method** method_addr()    { return &_method; }

 private:
  Method* _method;
  void set(Method* method)  { assert(method != NULL, "use clear"); _method = method; }
  void clear()                { _method = NULL; }
  void print()                                        PRODUCT_RETURN;
  void verify(klassVtable* vt, outputStream* st);

  friend class klassVtable;
};

// 获取 vtable 中指定索引的方法.
inline Method* klassVtable::method_at(int i) const {
  assert(i >= 0 && i < _length, "index out of bounds");
  assert(table()[i].method() != NULL, "should not be null");
  assert(((Metadata*)table()[i].method())->is_method(), "should be method");
  return table()[i].method();
}

inline Method* klassVtable::unchecked_method_at(int i) const {
  assert(i >= 0 && i < _length, "index out of bounds");
  return table()[i].method();
}

// --------------------------------------------------------------------------------
class klassItable;
class itableMethodEntry;

class itableOffsetEntry {
 private:
  InstanceKlass* _interface;
  int      _offset;
 public:
  InstanceKlass* interface_klass() const { return _interface; }
  InstanceKlass**interface_klass_addr()  { return &_interface; }
  int      offset() const          { return _offset; }

  static itableMethodEntry* method_entry(Klass* k, int offset) { return (itableMethodEntry*)(((address)k) + offset); }
  itableMethodEntry* first_method_entry(Klass* k)              { return method_entry(k, _offset); }

  void initialize(InstanceKlass* interf, int offset) { _interface = interf; _offset = offset; }

  // Static size and offset accessors
  static int size()                       { return sizeof(itableOffsetEntry) / wordSize; }    // size in words
  static int interface_offset_in_bytes()  { return offset_of(itableOffsetEntry, _interface); }
  static int offset_offset_in_bytes()     { return offset_of(itableOffsetEntry, _offset); }

  friend class klassItable;
};


class itableMethodEntry {
 private:
  Method* _method;

 public:
  Method* method() const { return _method; }
  Method**method_addr() { return &_method; }

  void clear()             { _method = NULL; }

  void initialize(Method* method);

  // Static size and offset accessors
  static int size()                         { return sizeof(itableMethodEntry) / wordSize; }  // size in words
  static int method_offset_in_bytes()       { return offset_of(itableMethodEntry, _method); }

  friend class klassItable;
};

//
// Format of an itable
//
//    ---- offset table ---
//    Klass* of interface 1             \
//    offset to vtable from start of oop  / offset table entry
//    ...
//    Klass* of interface n             \
//    offset to vtable from start of oop  / offset table entry
//    --- vtable for interface 1 ---
//    Method*                             \
//    compiler entry point                / method table entry
//    ...
//    Method*                             \
//    compiler entry point                / method table entry
//    -- vtable for interface 2 ---
//    ...
//
class klassItable {
 private:
  InstanceKlass*       _klass;             // my klass
  int                  _table_offset;      // offset of start of itable data within klass (in words)
  int                  _size_offset_table; // size of offset table (in itableOffset entries)
  int                  _size_method_table; // size of methodtable (in itableMethodEntry entries)

  void initialize_itable_for_interface(int method_table_offset, InstanceKlass* interf_h, bool checkconstraints, TRAPS);
 public:
  klassItable(InstanceKlass* klass);

  itableOffsetEntry* offset_entry(int i) { assert(0 <= i && i <= _size_offset_table, "index out of bounds");
                                           return &((itableOffsetEntry*)vtable_start())[i]; }

  itableMethodEntry* method_entry(int i) { assert(0 <= i && i <= _size_method_table, "index out of bounds");
                                           return &((itableMethodEntry*)method_start())[i]; }

  int size_offset_table()                { return _size_offset_table; }

  // Initialization
  void initialize_itable(bool checkconstraints, TRAPS);

#if INCLUDE_JVMTI
  // RedefineClasses() API support:
  // if any entry of this itable points to any of old_methods,
  // replace it with the corresponding new_method.
  // trace_name_printed is set to true if the current call has
  // printed the klass name so that other routines in the adjust_*
  // group don't print the klass name.
  void adjust_method_entries(bool* trace_name_printed);
  bool check_no_old_or_obsolete_entries();
  void dump_itable();
#endif // INCLUDE_JVMTI

  // Setup of itable
  static int assign_itable_indices_for_interface(InstanceKlass* klass, TRAPS);
  static int method_count_for_interface(InstanceKlass* klass);
  static int compute_itable_size(Array<InstanceKlass*>* transitive_interfaces);
  static void setup_itable_offset_table(InstanceKlass* klass);

  // Debugging/Statistics
  static void print_statistics() PRODUCT_RETURN;
 private:
  intptr_t* vtable_start() const { return ((intptr_t*)_klass) + _table_offset; }
  intptr_t* method_start() const { return vtable_start() + _size_offset_table * itableOffsetEntry::size(); }

  // Helper methods
  static int  calc_itable_size(int num_interfaces, int num_methods) { return (num_interfaces * itableOffsetEntry::size()) + (num_methods * itableMethodEntry::size()); }

  // Statistics
  NOT_PRODUCT(static int  _total_classes;)   // Total no. of classes with itables
  NOT_PRODUCT(static long _total_size;)      // Total no. of bytes used for itables

  static void update_stats(int size) PRODUCT_RETURN NOT_PRODUCT({ _total_classes++; _total_size += size; })
};

#endif // SHARE_OOPS_KLASSVTABLE_HPP
