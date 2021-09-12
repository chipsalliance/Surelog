#ifndef SURELOG_RTTI_H
#define SURELOG_RTTI_H

#pragma once

#include <array>
#include <cstdint>
#include <map>
#include <memory>
#include <type_traits>


namespace SURELOG
{
  // Ref: https://gist.github.com/klemens-morgenstern/b75599292667a4f53007
  namespace internal
  {
    template<std::size_t ... Size>
    struct num_tuple {};

    template<std::size_t Prepend, typename T>
    struct appender {};

    template<std::size_t Prepend, std::size_t ... Sizes>
    struct appender<Prepend, num_tuple<Sizes...>>
    {
      using type = num_tuple<Prepend, Sizes...>;
    };

    template<std::size_t Size, std::size_t Counter = 0>
    struct counter_tuple
    {
      using type = typename appender<Counter, typename counter_tuple<Size, Counter + 1>::type>::type;
    };

    template<std::size_t Size>
    struct counter_tuple<Size, Size>
    {
      using type = num_tuple<>;
    };

    template<typename T, std::size_t LL, std::size_t RL, std::size_t ... LLs, std::size_t ... RLs>
    constexpr std::array<T, LL + RL> join(
      const std::array<T, LL> rhs, const std::array<T, RL> lhs,
      internal::num_tuple<LLs...>, internal::num_tuple<RLs...>)
    {
      return { rhs[LLs]..., lhs[RLs]... };
    }

    template<typename T, std::size_t LL, std::size_t RL>
    constexpr std::array<T, LL + RL> join(std::array<T, LL> rhs, std::array<T, RL> lhs)
    {
      return join(
        rhs, lhs,
        typename internal::counter_tuple<LL>::type(),
        typename internal::counter_tuple<RL>::type());
    }

    static constexpr uint32_t kFNV1aSeed32 = 0x811C9DC5;
    static constexpr uint32_t kFNV1aPrime32 = 0x01000193;

    inline constexpr uint32_t RTTIHash(const char *const str, uint32_t hash) noexcept
    {
      return (*str == '\0')
        ? hash
        : RTTIHash(str + 1, (hash ^ static_cast<uint32_t>(*str)) * kFNV1aPrime32);
    }
  }

  class RTTI
  {
  protected:
    typedef uint32_t typeid_t;
    typedef RTTI thistype_t;
    static constexpr typeid_t kTypeId = internal::RTTIHash("RTTI", internal::kFNV1aSeed32);
    static constexpr std::array<typeid_t, 1> kTypeIds{ kTypeId };

  protected:
    RTTI() = default;

  public:
    virtual ~RTTI() = default;

  protected:
    virtual typeid_t GetTypeId() const = 0;
    virtual void *AsType(typeid_t id) = 0;
    virtual const void *AsType(typeid_t tid) const = 0;
    virtual const typeid_t *GetTypeIds(size_t &count) const = 0;

    inline bool IsOfType(typeid_t tid) const
    {
      size_t count = 0;
      const typeid_t *const typeIds = GetTypeIds(count);
      for (size_t i = 0; i < count; ++i)
      {
        if (typeIds[i] == tid)
          return true;
      }

      return false;
    }

  public:
    template<
      typename I,
      typename T = typename std::remove_pointer<I>::type,
      typename = typename std::enable_if<std::is_base_of<RTTI, T>::value>::type>
    inline T *VirtualCast()
    {
      return IsOfType(T::kTypeId) ? static_cast<T *>(AsType(T::kTypeId)) : nullptr;
    }

    template<
      typename I,
      typename T = typename std::remove_pointer<I>::type,
      typename = typename std::enable_if<std::is_base_of<RTTI, T>::value>::type>
    inline const T *VirtualCast() const
    {
      return IsOfType(T::kTypeId) ? static_cast<const T *>(AsType(T::kTypeId)) : nullptr;
    }

    template<
      typename I,
      typename T = typename std::remove_pointer<I>::type,
      typename = typename std::enable_if<std::is_base_of<RTTI, T>::value>::type>
    inline T *Cast()
    {
      return IsOfType(T::kTypeId) ? static_cast<T *>(this) : nullptr;
    }

    template<
      typename I,
      typename T = typename std::remove_pointer<I>::type,
      typename = typename std::enable_if<std::is_base_of<RTTI, T>::value>::type>
    inline const T *Cast() const
    {
      return IsOfType(T::kTypeId) ? static_cast<const T *>(this) : nullptr;
    }
  };

  inline RTTI::typeid_t RTTI::GetTypeId() const
  {
    return RTTI::kTypeId;
  }

  inline const RTTI::typeid_t *RTTI::GetTypeIds(size_t &count) const
  {
    count = kTypeIds.size();
    return kTypeIds.data();
  }

  inline void *RTTI::AsType(typeid_t tid)
  {
    return (tid == RTTI::kTypeId) ? static_cast<void *>(this) : nullptr;
  }

  inline const void *RTTI::AsType(typeid_t tid) const
  {
    return (tid == RTTI::kTypeId) ? static_cast<const void *>(this) : nullptr;
  }

} // namespace SURELOG

#define SURELOG_IMPLEMENT_RTTI(classType, baseType)                                                       \
  public:                                                                                                 \
    typedef classType thistype_t;                                                                         \
    typedef baseType basetype_t;                                                                          \
    static constexpr typeid_t kTypeId = internal::RTTIHash("/" #classType, basetype_t::kTypeId);          \
    static constexpr auto kTypeIds = internal::join(                                                      \
      std::array<typeid_t, 1>{thistype_t::kTypeId}, basetype_t::kTypeIds);                                \
  protected:                                                                                              \
    friend class RTTI;                                                                                    \
    inline virtual RTTI::typeid_t GetTypeId() const override { return thistype_t::kTypeId; }              \
    inline virtual const RTTI::typeid_t *GetTypeIds(size_t &count) const override                         \
    { count = thistype_t::kTypeIds.size(); return thistype_t::kTypeIds.data(); }                          \
    inline virtual void *AsType(typeid_t tid) override                                                    \
    { return (tid == thistype_t::kTypeId) ? static_cast<void *>(this) : basetype_t::AsType(tid); }        \
    inline virtual const void *AsType(typeid_t tid) const override                                        \
    { return (tid == thistype_t::kTypeId) ? static_cast<const void *>(this) : basetype_t::AsType(tid); }  \
  private:

#define SURELOG_IMPLEMENT_RTTI_2_BASES(classType, baseType1, baseType2)                                                           \
  public:                                                                                                                         \
    typedef classType thistype_t;                                                                                                 \
    typedef baseType1 base1type_t;                                                                                                \
    typedef baseType2 base2type_t;                                                                                                \
    static constexpr typeid_t kTypeId = internal::RTTIHash("/" #classType, base1type_t::kTypeId ^ base2type_t::kTypeId);          \
    static constexpr auto kTypeIds = internal::join(                                                                              \
      std::array<typeid_t, 1>{thistype_t::kTypeId},                                                                               \
      internal::join(base1type_t::kTypeIds, base2type_t::kTypeIds));                                                              \
  protected:                                                                                                                      \
    friend class RTTI;                                                                                                            \
    inline virtual RTTI::typeid_t GetTypeId() const override { return thistype_t::kTypeId; }                                      \
    inline virtual const RTTI::typeid_t *GetTypeIds(size_t &count) const override                                                 \
    { count = thistype_t::kTypeIds.size(); return thistype_t::kTypeIds.data(); }                                                  \
    inline virtual void *AsType(typeid_t tid) override {                                                                          \
      void *p = nullptr;                                                                                                          \
      if (tid == thistype_t::kTypeId) p = static_cast<void *>(this);                                                              \
      if (p == nullptr) p = base1type_t::AsType(tid);                                                                             \
      if (p == nullptr) p = base2type_t::AsType(tid);                                                                             \
      return p;                                                                                                                   \
    }                                                                                                                             \
    inline virtual const void *AsType(typeid_t tid) const override {                                                              \
      const void *p = nullptr;                                                                                                    \
      if (tid == thistype_t::kTypeId) p = static_cast<const void *>(this);                                                        \
      if (p == nullptr) p = base1type_t::AsType(tid);                                                                             \
      if (p == nullptr) p = base2type_t::AsType(tid);                                                                             \
      return p;                                                                                                                   \
    }                                                                                                                             \
  private:

#define SURELOG_IMPLEMENT_RTTI_CAST_FUNCTIONS(fname, baseType)                                                                          \
  template<                                                                                                                             \
    typename I,                                                                                                                         \
    typename T = typename std::remove_pointer<I>::type,                                                                                 \
    typename = typename std::enable_if<std::is_pointer<I>::value>::type,                                                                \
    typename = typename std::enable_if<std::is_base_of<baseType, T>::value>::type>                                                      \
  inline T *fname(baseType *const u) noexcept {                                                                                         \
    return (u == nullptr) ? nullptr : u->template Cast<T>();                                                                            \
  }                                                                                                                                     \
  template<                                                                                                                             \
    typename I,                                                                                                                         \
    typename T = typename std::remove_pointer<I>::type,                                                                                 \
    typename = typename std::enable_if<std::is_pointer<I>::value>::type,                                                                \
    typename = typename std::enable_if<std::is_base_of<baseType, T>::value>::type>                                                      \
  inline const T *fname(const baseType *const u) noexcept {                                                                             \
    return (u == nullptr) ? nullptr : u->template Cast<const T>();                                                                      \
  }                                                                                                                                     \
  template<typename T, typename = typename std::enable_if<std::is_base_of<baseType, T>::value>::type>                                   \
  inline std::shared_ptr<T> fname(std::shared_ptr<baseType> const &u) noexcept {                                                        \
    return (u && (u->template Cast<T>() != nullptr)) ? std::static_pointer_cast<T>(u) : std::shared_ptr<T>(nullptr);                    \
  }                                                                                                                                     \
  template<typename T, typename = typename std::enable_if<std::is_base_of<baseType, T>::value>::type>                                   \
  inline std::shared_ptr<const T> fname(std::shared_ptr<const baseType> const &u) noexcept {                                            \
    return (u && (u->template Cast<const T>() != nullptr)) ? std::static_pointer_cast<const T>(u) : std::shared_ptr<const T>(nullptr);  \
  }

#define SURELOG_IMPLEMENT_RTTI_VIRTUAL_CAST_FUNCTIONS(fname, baseType)                                                                        \
  template<                                                                                                                                   \
    typename I,                                                                                                                               \
    typename T = typename std::remove_pointer<I>::type,                                                                                       \
    typename = typename std::enable_if<std::is_pointer<I>::value>::type,                                                                      \
    typename = typename std::enable_if<std::is_base_of<baseType, T>::value>::type>                                                            \
  inline T *fname(baseType *const u) noexcept {                                                                                               \
    return (u == nullptr) ? nullptr : u->template VirtualCast<T>();                                                                           \
  }                                                                                                                                           \
  template<                                                                                                                                   \
    typename I,                                                                                                                               \
    typename T = typename std::remove_pointer<I>::type,                                                                                       \
    typename = typename std::enable_if<std::is_pointer<I>::value>::type,                                                                      \
    typename = typename std::enable_if<std::is_base_of<baseType, T>::value>::type>                                                            \
  inline const T *fname(const baseType *const u) noexcept {                                                                                   \
    return (u == nullptr) ? nullptr : u->template VirtualCast<const T>();                                                                     \
  }                                                                                                                                           \
  template<typename T, typename = typename std::enable_if<std::is_base_of<baseType, T>::value>::type>                                         \
  inline std::shared_ptr<T> fname(std::shared_ptr<baseType> const &u) noexcept {                                                              \
    return (u && (u->template VirtualCast<T>() != nullptr)) ? std::static_pointer_cast<T>(u) : std::shared_ptr<T>(nullptr);                   \
  }                                                                                                                                           \
  template<typename T, typename = typename std::enable_if<std::is_base_of<baseType, T>::value>::type>                                         \
  inline std::shared_ptr<const T> fname(std::shared_ptr<const baseType> const &u) noexcept {                                                  \
    return (u && (u->template VirtualCast<const T>() != nullptr)) ? std::static_pointer_cast<const T>(u) : std::shared_ptr<const T>(nullptr); \
  }

#endif  /// SURELOG_RTTI_H
