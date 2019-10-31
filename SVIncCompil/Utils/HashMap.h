
#ifndef HASHMAP_H
#define HASHMAP_H
#include <iostream>
#include <iomanip>
#include <exception>
#include <mutex>
#include <condition_variable>

/*
*  wrapper for items stored in the map
*/
template<typename K, typename V>
class HashItem {
public:
    HashItem(K key, V value) {
        this->key = key;
        this->value = value;
        this->nextItem = nullptr;
    }

    /*
    * copy constructor
    */
    HashItem(const HashItem & item) {
        this->key = item.getKey();
        this->value = item.getValue();
        this->nextItem = nullptr;
    }

    void setNext(HashItem<K, V> * item) {
        this->nextItem = item;
    }

    HashItem * getNext() {
        return nextItem;
    }

    K getKey() {
        return key;
    }

    V getValue() {
        return value;
    }

    void setValue(V value) {
        this->value = value;
    }

private:
    K key;
    V value;
    HashItem * nextItem;

};

/*
* template HashMap for storing items
* default hash function HF = std::hash<K>
*/
template <typename K, typename V, typename HF = std::hash<K>>
class HashMap {
public:
    /*
    * constructor
    * @mSize specifies the bucket size og the map
    */
    HashMap(std::size_t mSize) {
        // lock initialization for single thread
        std::lock_guard<std::mutex>lock(mtx);
        //if (mSize < 1)
            //throw std::exception("Number of buckets ust be greater than zero.");

        mapSize = mSize;
        numOfItems = 0;
        // initialize
        hMap = new HashItem<K, V> *[mapSize]();
    }

    /*
    * for simplicity no copy constructor
    * anyway we want test how different threads 
    * use same instance of the map
    */
    //HashMap(const HashMap & hmap) = delete;

    /*
    * inserts item
    * replaces old value with the new one when item already exists
    * @key key of the item
    * @value value of the item
    */
    void insert(const K & key, const V & value) {
        std::lock_guard<std::mutex>lock(mtx);
        insertHelper(this->hMap, this->mapSize, numOfItems, key, value);
        condVar.notify_all();
    }

    /*
    * erases item with key when siúch item exists
    * @key of item to erase
    */
    void erase(const K & key) {
        std::lock_guard<std::mutex>lock(mtx);
        // calculate the bucket where item must be inserted
        std::size_t hVal = hashFunc(key) % mapSize;
        HashItem<K, V> * prev = nullptr;
        HashItem<K, V> * item = hMap[hVal];

        while ((item != nullptr) && (item->getKey() != key)) {
            prev = item;
            item = item->getNext();
        }
        // no item found with the given key
        if (item == nullptr) {
            return;
        }
        else {
            if (prev == nullptr) {
                // item found is the first item in the bucket
                hMap[hVal] = item->getNext();
            }
            else {
                // item found in one of the entries in the bucket
                prev->setNext(item->getNext());
            }
            delete item;
            numOfItems--;
        }
        condVar.notify_all();
    }

    /*
    * get element with the given key by reference
    * @key is the key of item that has to be found
    * @value is the holder where the value of item with key will be copied
    */
    bool getItem(const K & key, V & value) const {
        std::lock_guard<std::mutex>lock(mtx);
        // calculate the bucket where item must be inserted
        std::size_t hVal = hashFunc(key) % mapSize;
        HashItem<K, V> * item = hMap[hVal];

        while ((item != nullptr) && (item->getKey() != key))
            item = item->getNext();
        // item not found
        if (item == nullptr) {
            return false;
        }

        value = item->getValue();
        return true;
    }


    /*
    * get element with the given key by reference
    * @key is the key of item that has to be found
    * shows an example of thread waitung for some condition
    * @value is the holder where the value of item with key will be copied
    */
    bool getWithWait(const K & key, V & value) {
        std::unique_lock<std::mutex>ulock(mtxForWait);
        condVar.wait(ulock, [this] {return !this->empty(); });
        // calculate the bucket where item must be inserted
        std::size_t hVal = hashFunc(key) % mapSize;
        HashItem<K, V> * item = hMap[hVal];

        while ((item != nullptr) && (item->getKey() != key))
            item = item->getNext();
        // item not found
        if (item == nullptr) {
            return false;
        }

        value = item->getValue();
        return true;
    }


    /*
    * resizes the map
    * creates new map on heap
    * copies the elements into new map
    * @newSize specifies new bucket size
    */
    void resize(std::size_t newSize) {
        std::lock_guard<std::mutex>lock(mtx);
        if (newSize < 1)
            throw std::exception("Number of buckets must be greater than zero.");

        resizeHelper(newSize);
        condVar.notify_all();
    }

    /*
    * outputs all items of the map
    */
    void outputMap() const {
        std::lock_guard<std::mutex>lock(mtx);
        if (numOfItems == 0) {
            std::cout << "Map is empty." << std::endl << std::endl;
            return;
        }
        std::cout << "Map contains " << numOfItems << " items." << std::endl;
        for (std::size_t i = 0; i < mapSize; i++) {
            HashItem<K, V> * item = hMap[i];
            while (item != nullptr) {
                std::cout << "Bucket: " << std::setw(3) << i << ", key: " << std::setw(3) << item->getKey() << ", value:" << std::setw(3) << item->getValue() << std::endl;
                item = item->getNext();
            }
        }
        std::cout << std::endl;
    }

    /*
    * returns true when map has no items
    */
    bool empty() const {
        std::lock_guard<std::mutex>lock(mtx);
        return numOfItems == 0;
    }

    void clear() {
        std::lock_guard<std::mutex>lock(mtx);
        deleteMap(hMap, mapSize);
        numOfItems = 0;
        hMap = new HashItem<K, V> *[mapSize]();
    }
    
     void deleteDeep() {
        std::lock_guard<std::mutex>lock(mtx);
        deleteMapDeep(hMap, mapSize);
        numOfItems = 0;
        hMap = new HashItem<K, V> *[mapSize]();
    }

    /*
    * returns number of items stored in the map
    */
    std::size_t size() const {
        std::lock_guard<std::mutex>lock(mtx);
        return numOfItems;
    }

    /*
    * returns number of buckets
    */
    std::size_t bucket_count() const {
        std::lock_guard<std::mutex>lock(mtx);
        return mapSize;
    }

    /*
    * desctructor
    */
    ~HashMap() {
        std::lock_guard<std::mutex>lock(mtx);
        deleteMap(hMap, mapSize);
    }

private:
    std::size_t mapSize;
    std::size_t numOfItems;
    HF hashFunc;
    HashItem<K, V> ** hMap;
    mutable std::mutex mtx;
    mutable std::mutex mtxForWait;
    std::condition_variable condVar;

    /*
    * help method for inserting key, value item into the map hm
    * mapSize specifies the size of the map, items - the number
    * of stored items, will be incremented when insertion is completed
    * @hm HashMap
    * @mSize specifies number of buckets
    * @items holds the number of items in hm, will be incremented when insertion successful
    * @key - key of item to insert
    * @value - value of item to insert
    */
    void insertHelper(HashItem<K, V> ** hm, const std::size_t & mSize, std::size_t & items, const K & key, const V & value) {
        std::size_t hVal = hashFunc(key) % mSize;
        HashItem<K, V> * prev = nullptr;
        HashItem<K, V> * item = hm[hVal];

        while ((item != nullptr) && (item->getKey() != key)) {
            prev = item;
            item = item->getNext();
        }

        // inserting new item
        if (item == nullptr) {
            item = new HashItem<K, V>(key, value);
            items++;
            if (prev == nullptr) {
                // insert new value as first item in the bucket
                hm[hVal] = item;
            }
            else {
                // append new item on previous in the same bucket
                prev->setNext(item);
            }
        }
        else {
            // replace existing value
            item->setValue(value);
        }
    }

    /*
    * help method to resize the map
    * @newSize specifies new number of buckets
    */
    void resizeHelper(std::size_t newSize) {
        HashItem<K, V> ** newMap = new HashItem<K, V> *[newSize]();
        std::size_t items = 0;
        for (std::size_t i = 0; i < mapSize; i++) {
            HashItem<K, V> * item = hMap[i];
            while (item != nullptr) {
                insertHelper(newMap, newSize, items, item->getKey(), item->getValue());
                item = item->getNext();
            }
        }

        deleteMap(hMap, mapSize);
        hMap = newMap;
        mapSize = newSize;
        numOfItems = items;
        newMap = nullptr;

    }

    /*
    * help function for deleting the map hm
    * @hm HashMap
    * @mSize number of buckets in hm
    */
    void deleteMap(HashItem<K, V> ** hm, std::size_t mSize) {
        // delete all nodes
        for (std::size_t i = 0; i < mSize; ++i) {
            HashItem<K, V> * item = hm[i];
            while (item != nullptr) {
                HashItem<K, V> * prev = item;
                item = item->getNext();
                delete prev;
            }
            hm[i] = nullptr;
        }
        // delete the map
        delete[] hm;
    }
    
       /*
    * help function for deleting the map hm
    * @hm HashMap
    * @mSize number of buckets in hm
    */
    void deleteMapDeep(HashItem<K, V> ** hm, std::size_t mSize) {
        // delete all nodes
        for (std::size_t i = 0; i < mSize; ++i) {
            HashItem<K, V> * item = hm[i];
            while (item != nullptr) {
                HashItem<K, V> * prev = item;
                item = item->getNext();
                delete prev->getValue();
                delete prev;
            }
            hm[i] = nullptr;
        }
        // delete the map
        delete[] hm;
    }
    
    
};

#endif /* HASHMAP_H */




