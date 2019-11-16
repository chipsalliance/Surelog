/******************************************************************************
 * (C) Copyright 2014 AMIQ Consulting
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NAME:        amiq_eth_packer.cpp
 * PROJECT:     amiq_eth
 * Description: This file declares the packer used in packing/unpacking of the
 * 				Ethernet packets
 *******************************************************************************/

//the block size - used in avoiding memory re-allocations at every pack action
#define AMIQ_ETH_PACKING_BLOCK_SIZE 4096

//class for packing and unpacking the Ethernet packets
class amiq_eth_packer {

private:

	//pack index
	unsigned int pack_index;

	//unpack index
	unsigned int unpack_index;

	//information bits
	sc_bv_base* information_bits;

	//the current size (in memory blocks)
	int size;

	//the maximum size (in memory blocks)
	int max_size;

protected:

	//method for allocating required memory
	//@param - number_of_bits - number of bits requested to be packed
	void allocate(int number_of_bits) {
		//number of bits which will be packed
		int total_bits = pack_index + number_of_bits;

		//the new size (in memory blocks) required to hold the entire information
		size = ((total_bits - 1) / AMIQ_ETH_PACKING_BLOCK_SIZE + 1) * AMIQ_ETH_PACKING_BLOCK_SIZE;

		if (size > max_size) {
			//the new size exceeds the current allocated memory space so new allocation must be done

			//allocate a new memory region of required size
			sc_bv_base* new_bv = new sc_bv_base(size);

			if (information_bits) {
				//save the current information
				*new_bv = *information_bits;

				//delete the old memory location of the information bits
				delete information_bits;
			}

			information_bits = new_bv;

			//save the current allocated size
			max_size = size;
		}
	}

	//method for checking the number of bits requested to be packed
	//@param - number_of_bits - number of bits requested to be packed
	void check_size(int number_of_bits) {
		//determine the current free space
		int free_space = size - pack_index;

		if (number_of_bits >= free_space) {
			//the number of bits requested to be packed is bigger then the available free space
			//so new memory allocation is required
			allocate(number_of_bits);
		}
	}

	//method for incrementing the unpacking index
	//@param - number_of_bits - number of bits to be unpacked
	void inc_unpack_index(int number_of_bits) {
		unpack_index += number_of_bits;
		if (unpack_index > pack_index) {
			char msg[1024];
			sprintf(msg, "Trying to unpack more information then it was packed so far - unpack_index=%d, pack_index=%d", unpack_index, pack_index);
			SC_REPORT_ERROR("AMIQ_ETH", msg);
		}
	}

	//method for packing an integer
	//@param data - data to be packed
	//@param - number_of_bits - number of bits used to pack "data"
	void pack_int_n(unsigned long long data, unsigned number_of_bits) {
		check_size(number_of_bits);
		(*information_bits)(pack_index + number_of_bits - 1, pack_index) = data;
		pack_index += number_of_bits;
	}

	//method for unpacking an integer
	//@param - number_of_bits - number of bits to be unpacked
	//@return - the unpacked integer
	uint64 unpack_int_n(unsigned number_of_bits) {
		uint64 data;
		data = (*information_bits)(unpack_index + number_of_bits - 1, unpack_index).to_uint64();
		inc_unpack_index(number_of_bits);
		return data;
	}

public:

	//constructor
	amiq_eth_packer() {
		pack_index = 0;
		unpack_index = 0;
		size = 0;
		max_size = 0;
		information_bits = 0;
	}

	//destructor
	virtual ~amiq_eth_packer() {
		if (information_bits) {
			delete information_bits;
		}
	}

	//packing operator
	virtual amiq_eth_packer& operator <<(bool a) {
		int bit_value = a ? 1 : 0;
		pack_int_n(bit_value, 1);
		return *this;
	}

	//unpacking operator
	virtual amiq_eth_packer& operator >>(bool& a) {
		a = (bool) (unpack_int_n(1));
		return *this;
	}

	//reset the packer
	virtual void reset() {
		pack_index = 0;
		unpack_index = 0;
		size = 0;
	}

	//method for returning the number of remaining unpacked bits
	//@return number of unpacked bits
	virtual int get_remaining_unpacked_bits() {
		return pack_index - unpack_index;
	}

	//method for getting a vector of bytes
	//@param data - vector of bytes
	void get_bytes(std::vector<char>& data) {
		unsigned n = get_remaining_unpacked_bits();
		unsigned nbytes = 1 + (n - 1) / 8;
		for (unsigned i = 0; i < nbytes; i++) {
			char b = (*information_bits).range(8 * i + 7, 8 * i).to_int();
			data.push_back(b);
		}
	}

};
