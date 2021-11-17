++__i)
        *__i = __x;
    if (__i == __e)
        insert(__e, __n, __x);
    else
        erase(__i, __e);
#if _LIBCPP_DEBUG_LEVEL >= 2
      __get_db()->__invalidate_all(this);
#endif
}

template <class _Tp, class _Alloc>
inline
_Alloc
list<_Tp, _Alloc>::get_allocator() const _NOEXCEPT
{
    return allocator_type(base::__node_alloc());
}

template <class _Tp, class _Alloc>
typename list<_Tp, _Alloc>::iterator
list<_Tp, _Alloc>::insert(const_iterator __p, const value_type& __x)
{
#if _LIBCPP_DEBUG_LEVEL >= 2
    _LIBCPP_ASSERT(__get_const_db()->__find_c_from_i(&__p) == this,
        "list::insert(iterator, x) called with an iterator not"
        " referring to this list");
#endif
    __node_allocator& __na = base::__node_alloc();
    typedef __allocator_destructor<__node_allocator> _Dp;
    unique_ptr<__node, _Dp> __hold(__node_alloc_traits::allocate(__na, 1), _Dp(__na, 1));
    __hold->__prev_ = 0;
    __node_alloc_traits::construct(__na, _VSTD::addressof(__hold->__value_), __x);
    __link_nodes(__p.__ptr_, __hold->__as_link(), __hold->__as_link());
    ++base::__sz();
#if _LIBCPP_DEBUG_LEVEL >= 2
    return iterator(__hold.release()->__as_link(), this);
#else
    return iterator(__hold.release()->__as_link());
#endif
}

template <clas